from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from functools import cache, reduce
from itertools import accumulate, islice, repeat
from operator import mul
from pathlib import Path
from struct import pack, unpack


class VerificationError(Exception):
    """Invalid proof."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


# Field arithmetic ------------------------------------------------------------


def _base_mul(left: int, right: int) -> int:
    product = 0
    while right:
        if right & 1:
            product ^= left
        right >>= 1
        left <<= 1
    low, high = product & (2**64 - 1), product >> 64
    folded = low ^ high ^ (high << 1) ^ (high << 3) ^ (high << 4)
    overflow = folded >> 64
    return ((folded & (2**64 - 1)) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & (2**64 - 1)


@dataclass(frozen=True, slots=True)
class K:
    """GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1)"""

    value: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.value, int) or isinstance(self.value, bool) or not 0 <= self.value <= (2**64 - 1):
            raise ValueError("a K element is a 64-bit unsigned integer")

    def __index__(self) -> int:
        return self.value

    def to_bytes(self) -> bytes:
        """Its transport image: one 64-bit little-endian word."""
        return self.value.to_bytes(8, "little")

    def __bool__(self) -> bool:
        return bool(self.value)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, K):
            return self.value == other.value
        return isinstance(other, int) and not isinstance(other, bool) and self.value == other

    def __hash__(self) -> int:
        return hash(self.value)

    def __add__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(self.value ^ rhs.value)

    __radd__ = __add__

    def __mul__(self, other: object) -> K:
        rhs = _as_k(other)
        return NotImplemented if rhs is None else K(_base_mul(self.value, rhs.value))

    __rmul__ = __mul__

    def __repr__(self) -> str:
        return f"K(0x{self.value:016x})"


def _as_k(value: object) -> K | None:
    if isinstance(value, K):
        return value
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value <= 2**64 - 1:
        return K(value)
    return None


@dataclass(frozen=True, slots=True, init=False)
class E:
    """K[y]/(y^3 + y + 1): the challenge field, a degree-3 extension of K. Limbs may be given as plain integers, which are lifted."""

    c0: K
    c1: K
    c2: K

    def __init__(self, c0: K | int = 0, c1: K | int = 0, c2: K | int = 0) -> None:
        object.__setattr__(self, "c0", c0 if isinstance(c0, K) else K(c0))
        object.__setattr__(self, "c1", c1 if isinstance(c1, K) else K(c1))
        object.__setattr__(self, "c2", c2 if isinstance(c2, K) else K(c2))

    @classmethod
    def from_bytes(cls, data: bytes) -> E:
        require(len(data) == 24, "a field element must contain exactly 24 bytes")
        return cls(*unpack("<3Q", data))

    def to_bytes(self) -> bytes:
        return pack("<3Q", self.c0, self.c1, self.c2)

    @staticmethod
    def lift(value: object) -> E:
        """`value` as an extension element; anything that is not one is an error."""
        if isinstance(value, E):
            return value
        lifted = _as_k(value)
        if lifted is not None:
            return E(lifted)
        raise TypeError(f"cannot use {type(value).__name__} as a field element")

    @staticmethod
    def sum(values: Iterable[E]) -> E:
        return sum(values, ZERO)

    def __int__(self) -> int:
        return self.c0.value | self.c1.value << 64 | self.c2.value << 128

    def __bool__(self) -> bool:
        return bool(self.c0 or self.c1 or self.c2)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, E):
            return self.c0 == other.c0 and self.c1 == other.c1 and self.c2 == other.c2
        return not (self.c1 or self.c2) and self.c0 == other

    def __hash__(self) -> int:
        return hash(int(self))

    def __add__(self, other: object) -> E:
        rhs = self.lift(other)
        return E(self.c0 + rhs.c0, self.c1 + rhs.c1, self.c2 + rhs.c2)

    __radd__ = __add__

    def __mul__(self, other: object) -> E:
        rhs = self.lift(other)
        # y^3 = y + 1 folds the degree-4 product back into three limbs.
        p0 = self.c0 * rhs.c0
        p1 = self.c0 * rhs.c1 + self.c1 * rhs.c0
        p2 = self.c0 * rhs.c2 + self.c1 * rhs.c1 + self.c2 * rhs.c0
        p3 = self.c1 * rhs.c2 + self.c2 * rhs.c1
        p4 = self.c2 * rhs.c2
        return E(p0 + p3, p1 + p3 + p4, p2 + p4)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> E:
        if exponent < 0:
            return self.inv() ** -exponent
        base, out, n = self, ONE, exponent
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n >>= 1
        return out

    def inv(self) -> E:
        require(bool(self), "division by zero in GF(2^192)")
        return self ** (2**192 - 2)

    def __truediv__(self, other: object) -> E:
        rhs = self.lift(other)
        return self * rhs.inv()

    def __repr__(self) -> str:
        return f"E(0x{self.c2.value:016x}{self.c1.value:016x}{self.c0.value:016x})"


ZERO = E(0)
ONE = E(1)
GEN = E(2)


def powers(base: E, count: int) -> list[E]:
    """`[1, base, base^2, ...]`, `count` terms."""
    return list(islice(accumulate(repeat(base), mul, initial=ONE), count))


# BLAKE2s and digests ---------------------------------------------------------

BLAKE2S_IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)  # fmt: skip
BLAKE2S_SIGMA = ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15), (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3), (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4), (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8), (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13), (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9), (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11), (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10), (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5), (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0))  # fmt: skip
BLAKE2S_G_LANES = ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14))  # fmt: skip


def blake2s_hash(data: bytes) -> Digest:
    """Standard 32-byte unkeyed BLAKE2s-256 hash."""
    return Digest(hashlib.blake2s(data).digest())


@dataclass(frozen=True, slots=True)
class Digest:
    """256 bits"""

    value: bytes

    def __post_init__(self) -> None:
        require(len(self.value) == 32, "a digest is 256 bits")

    def words(self) -> tuple[int, int, int, int]:
        """Its four 64-bit words, the form the compression chain runs in."""
        return unpack("<4Q", self.value)

    @classmethod
    def from_halves(cls, low: E, high: E) -> Digest:
        """A digest as it travels on the stream: two 128-bit halves."""
        require(not (low.c2 or high.c2), "a digest half is 128-bit")
        return cls(pack("<4Q", low.c0, low.c1, high.c0, high.c1))


# Multilinear and stacking helpers --------------------------------------------


type MultilinearPoint = tuple[E, ...]


def eq_kernel(point: Sequence[E]) -> list[E]:
    out = [ONE]
    for r in point:
        out = [v * (ONE + r) for v in out] + [v * r for v in out]
    return out


def multilinear_eval(mle: Sequence[K | E], point: Sequence[E]) -> E:
    require(len(mle) == 2 ** len(point), "multilinear table has the wrong size")
    cur = [E.lift(value) for value in mle]
    for r in point:
        cur = [cur[2 * i] * (ONE + r) + cur[2 * i + 1] * r for i in range(len(cur) // 2)]
    return cur[0]


def log2_ceil(value: int) -> int:
    return max(0, (value - 1).bit_length())


def log2_strict(value: int) -> int:
    require(value > 0 and not value & (value - 1), "expected a power of two")
    return value.bit_length() - 1


def eq_eval(left: Sequence[E], right: Sequence[E]) -> E:
    result = ONE
    for x, y in zip(left, right, strict=True):
        result *= ONE + x + y
    return result


def dot(left: Sequence[K | E], right: Sequence[K | E]) -> E:
    result = ZERO
    for x, y in zip(left, right, strict=True):
        result += E.lift(x) * y
    return result


def powers_mle(first: E, ratio: E, point: MultilinearPoint) -> E:
    """MLE of ``[first * ratio^z]`` at an LSB-first point. No such column is ever committed: this is its evaluation."""
    result = first
    ratio_power = ratio
    for challenge in point:
        result *= ONE + challenge * (ONE + ratio_power)
        ratio_power **= 2
    return result


def index_mle(point: MultilinearPoint) -> E:
    """MLE of ``[1, g, g^2, ...]`` at an LSB-first point."""
    return powers_mle(ONE, GEN, point)


def poly_eval(coefficients: Sequence[E], point: E) -> E:
    """A polynomial at `point`, by Horner over its coefficients, constant first."""
    return reduce(lambda acc, c: acc * point + c, reversed(coefficients), ZERO)


@dataclass(frozen=True)
class Placement:
    """Where something sits in the stacked cube: a claim's point fills the `variables` coordinates above `low`, the bits of `index` fixing the rest.
    `low` is zero for a block with a cube of its own, and the slot width for a column interleaved into a bigger block."""

    variables: int
    index: int
    low: int = 0

    def stack_point(self, point: MultilinearPoint, stack_log: int) -> MultilinearPoint:
        bits = _selector_point(self.index, stack_log)
        return bits[: self.low] + tuple(point) + bits[self.low + self.variables :]

    def eq_above(self, point: Sequence[E]) -> E:
        """eq weight of the coordinates above the window."""
        bits = _selector_point(self.index >> (self.low + self.variables), len(point) - self.low - self.variables)
        return eq_eval(bits, point[self.low + self.variables :])


def stack_offsets(sizes: Sequence[int]) -> tuple[list[int], int]:
    offsets = [0] * len(sizes)
    total = 0
    for index, size in sorted(enumerate(sizes), key=lambda item: (-item[1], item[0])):
        offsets[index] = total
        total += 2**size
    return offsets, log2_ceil(total)


def _selector_point(selector: int, length: int) -> MultilinearPoint:
    return tuple(E(selector >> bit & 1) for bit in range(length))


# Proof transport ------------------------------------------------------------


@dataclass(frozen=True)
class Proof:
    stream: tuple[E, ...]
    merkle_openings: bytes

    @classmethod
    def load(cls, stream: Path, merkle_openings: Path) -> Proof:
        data = stream.read_bytes()
        require(len(data) % 24 == 0, "the stream is not a whole number of field elements")
        return cls(tuple(E.from_bytes(data[at : at + 24]) for at in range(0, len(data), 24)), merkle_openings.read_bytes())


# Fiat--Shamir ---------------------------------------------------------------

DS_OBSERVE = 1
DS_SQUEEZE = 2
DS_POW_BASE = 3
DS_POW_NONCE = 4


def compress(left: Sequence[K | int], right: Sequence[K | int]) -> tuple[int, int, int, int]:
    """Hash two four-word operands, a word being a plain integer or the K element standing for it."""
    return unpack("<4Q", blake2s_hash(b"".join(int(x).to_bytes(8, "little") for x in (*left, *right))).value)


class Transcript:
    def __init__(self, proof: Proof, fiat_shamir_IV: Digest, public_input: Sequence[K]) -> None:
        self.proof = proof
        self.state = compress(fiat_shamir_IV.words(), public_input)
        self.stream_offset = 0  # in E field elements
        self.opening_offset = 0  # in bytes

    def observe(self, value: E) -> None:
        self.state = compress(self.state, (value.c0, value.c1, value.c2, DS_OBSERVE))

    def sample(self) -> E:
        self.state = compress(self.state, (0, 0, 0, DS_SQUEEZE))
        return E(*self.state[:3])

    def samples(self, count: int) -> list[E]:
        return [self.sample() for _ in range(count)]

    def _next(self) -> E:
        require(self.stream_offset < len(self.proof.stream), "proof stream exhausted")
        value = self.proof.stream[self.stream_offset]
        self.stream_offset += 1
        return value

    def next_scalar(self) -> E:
        value = self._next()
        self.observe(value)
        return value

    def next_scalars(self, count: int) -> list[E]:
        return [self.next_scalar() for _ in range(count)]

    def grind_check(self, bits: int) -> None:
        nonce = self._next()
        block = (nonce.c0, nonce.c1, nonce.c2, DS_POW_NONCE)
        digest = compress(compress(self.state, (0, 0, 0, DS_POW_BASE)), block)[0]
        valid = nonce == ZERO if bits == 0 else digest & (2**bits - 1) == 0
        self.state = compress(self.state, block)
        require(valid, "invalid grinding nonce")

    def _merkle_data(self, length: int) -> bytes:
        end = self.opening_offset + length
        require(end <= len(self.proof.merkle_openings), "Merkle opening missing")
        chunk = self.proof.merkle_openings[self.opening_offset : end]
        self.opening_offset = end
        return chunk

    def merkle(self, root: Digest, block_length: int, queries: Sequence[int], leaf_words: int) -> list[tuple[K, ...]]:
        height = log2_strict(block_length)
        rows = []
        for query in queries:
            leaf = self._merkle_data(8 * leaf_words)
            node = blake2s_hash(leaf)
            for level in range(height):
                sibling = self._merkle_data(32)
                left, right = (node.value, sibling) if query >> level & 1 == 0 else (sibling, node.value)
                node = blake2s_hash(left + right)
            require(node == root, "Merkle root mismatch")
            rows.append(tuple(K(word) for word in unpack(f"<{leaf_words}Q", leaf)))
        return rows

    def sumcheck_round_poly(self, count: int, claim: E, eq_factor: E | None = None) -> list[E]:
        """returns q(X) := c0 + c1X + c2X^2 + ..."""
        if eq_factor is None:
            constant, tail = self.next_scalar(), self.next_scalars(count - 2)  # `q(0) + q(1) == claim`. The transcript contains c0, c2, c3 ...
            return [constant, claim + E.sum(tail), *tail]
        # `(1 + r) q(0) + r q(1) == claim`. The transcript contains c1, c2, c3 ... (r := eq_factor)
        tail = self.next_scalars(count - 1)
        return [claim + eq_factor * E.sum(tail), *tail]

    def finish(self) -> None:
        require(self.stream_offset == len(self.proof.stream), "proof stream not fully consumed")
        require(self.opening_offset == len(self.proof.merkle_openings), "Merkle openings not fully consumed")


def sumcheck(transcript: Transcript, claim: E, count: int, equalities: Sequence[E | None]) -> tuple[MultilinearPoint, E]:
    point = []
    for equality in equalities:
        message = transcript.sumcheck_round_poly(count, claim, equality)
        challenge = transcript.sample()
        point.append(challenge)
        claim = poly_eval(message, challenge)
    return tuple(point), claim


# Bus balance and decomposition ---------------------------------------------


def verify_gkr_grand_products(depth: int, transcript: Transcript) -> tuple[E, MultilinearPoint, tuple[E, E, E]]:
    shared, count = transcript.next_scalar(), transcript.next_scalar()
    combiner = transcript.sample()
    point: list[E] = []
    values = (shared, shared, count)  # 3 grand product GKR are batched together: push, pull, count

    layer = depth
    while layer > 0:
        # Two levels a step. An odd depth starts with one.
        step = 1 if layer % 2 else 2
        claim = poly_eval(values, combiner)
        # The product is degree 2^step, so one more coefficient than that per round.
        x, claim = sumcheck(transcript, claim, 2**step + 1, point)

        children = [transcript.next_scalars(2**step) for _ in range(3)]
        products = [reduce(mul, child) for child in children]
        require(claim == poly_eval(products, combiner), f"GKR layer {layer}: children do not match the sumcheck")

        y = transcript.samples(step)
        values = [multilinear_eval(child, y) for child in children]
        combiner = transcript.sample()
        point = [*y, *x]
        layer -= step

    return count, tuple(point), (values[0], values[1], values[2])


@dataclass
class Form:
    """A polynomial of degree at most 2 in a table's columns."""

    terms: dict[tuple[int, ...], E] = field(default_factory=dict)  # monomial -> coefficient; () is 1, (i,) is x_i, (i, j) is x_i*x_j

    def add_scaled(self, other: Form, weight: E) -> None:
        for monomial, coefficient in other.terms.items():
            self.terms[monomial] = self.terms.get(monomial, ZERO) + weight * coefficient

    def __add__(self, other: Form) -> Form:
        combined = Form(dict(self.terms))
        combined.add_scaled(other, ONE)
        return combined

    @staticmethod
    def sum(forms: Iterable[Form]) -> Form:
        """`Σ forms`, the empty sum being the zero polynomial."""
        return sum(forms, Form())

    def evaluate(self, column: Callable[[int], E]) -> E:
        return E.sum(reduce(mul, map(column, monomial), c) for monomial, c in self.terms.items())


@dataclass(frozen=True)
class BusBlock:
    """One block of a bus side, always owned by a table. The five blocks no table owns are the framework, on `BusLayout`."""

    log_rows: int  # the owner's height: this block flushes 2^log_rows rows
    coordinates: tuple[Form, ...]  # the tuple flushed, over the owner's OWN local column indices; stays symbolic until its table sumcheck
    owner: int  # whose block it is, by opcode


@dataclass(frozen=True)
class BusLayout:
    """Where a side's blocks sit in the stacked leaf cube. Split by kind because framework coordinates are
    public, so the verifier evaluates their fingerprints outright, while a table's stay symbolic until its sumcheck."""

    depth: int  # log2 of the padded cube, so how many layers the side's GKR walks
    framework: tuple[
        Placement, ...
    ]  # the blocks no table owns, stacked first: boundary state, memory, bytecode, the two range arrays (none on the count side)
    tables: tuple[Placement, ...]  # one per block a table owns, in the side's own block order


FrameworkLogRows = tuple[int, int, int, int, int] | tuple[()]  # state, memory, bytecode, range low, range high


def bus_layout(framework_log_rows: FrameworkLogRows, blocks: Sequence[BusBlock]) -> BusLayout:
    sizes = [*framework_log_rows, *(block.log_rows for block in blocks)]
    offsets, depth = stack_offsets(sizes)
    placements = [Placement(size, offset) for size, offset in zip(sizes, offsets)]
    split = len(framework_log_rows)
    return BusLayout(depth, tuple(placements[:split]), tuple(placements[split:]))


@dataclass(frozen=True)
class ColumnClaim:
    column: int
    point: MultilinearPoint
    value: E

    def on_stack(self, layout: Layout) -> StackClaim:
        point = layout.placements[self.column].stack_point(self.point, layout.stack_log)
        return (lambda x: eq_eval(point, x), self.value)


BUS_BITS = 4  # bus communicates tuples of 2^BUS_BITS field elements


@dataclass(frozen=True)
class BusResult:
    claims: tuple[ColumnClaim, ...]
    point: MultilinearPoint  # the GKR point zeta, which the table sumcheck reuses
    forms: tuple[tuple[Form, ...], ...]  # forms[table][side]
    totals: tuple[E, E, E]  # what the tables owe each side, derived


def verify_bus_balance(layout: Layout, transcript: Transcript) -> BusResult:
    framework_log_rows = (0, layout.log_memory, layout.log_bytecode, RANGE_LOG, RANGE_LOG)  # state, memory, bytecode, the two range arrays
    push_layout = bus_layout(framework_log_rows, layout.push)
    pull_layout = bus_layout(framework_log_rows, layout.pull)
    count_layout = bus_layout((), layout.count)

    alphas = transcript.samples(BUS_BITS)
    weights = eq_kernel(alphas)
    beta = transcript.sample()
    count_root, point, tree_values = verify_gkr_grand_products(push_layout.depth, transcript)
    require(count_root != ZERO, "a bus count is zero")

    # The framework blocks' committed columns, in the order the two sides first
    # name them: the initial memory on push, then on pull the final timestamps, the
    # final memory, and each read-only array's final counts.
    memory_low = tuple(point[: layout.log_memory])
    bytecode_low = tuple(point[: layout.log_bytecode])
    range_low = tuple(point[:RANGE_LOG])
    memory_initial = transcript.next_scalar()
    memory_final_ts = transcript.next_scalar()
    memory_final = transcript.next_scalar()
    bytecode_final = transcript.next_scalar()
    range_lo_final = transcript.next_scalar()
    range_hi_final = transcript.next_scalar()
    claims = [
        ColumnClaim(MEMORY_INITIAL, memory_low, memory_initial),
        ColumnClaim(MEMORY_FINAL_TIMESTAMPS, memory_low, memory_final_ts),
        ColumnClaim(MEMORY_FINAL, memory_low, memory_final),
        ColumnClaim(BYTECODE_FINAL_COUNTERS, bytecode_low, bytecode_final),
        ColumnClaim(RANGE_LO_FINAL_COUNTERS, range_low, range_lo_final),
        ColumnClaim(RANGE_HI_FINAL_COUNTERS, range_low, range_hi_final),
    ]
    memory_index = index_mle(memory_low)
    bytecode_index = index_mle(bytecode_low)
    bytecode_value = multilinear_eval(layout.bytecode, (*bytecode_low, *alphas))
    # The range arrays are never committed: their addresses g^(j+1) and g^(-2^16 j) are geometric.
    range_lo_index = powers_mle(GEN, GEN, range_low)
    range_hi_index = powers_mle(ONE, RANGE_HI_RATIO, range_low)

    def fingerprints(pc: E, clock: E, memory_ts: E, memory: E, bytecode_count: E, range_lo_count: E, range_hi_count: E) -> tuple[E, ...]:
        """The five framework tuples, each its coordinates weighted by eq(alpha, .); slots past the ones
        named are zero. A side differs only here: push starts the run and seeds every array, pull ends the
        run at the last pc and finalizes every array with its committed columns. Both boundaries sit in frame 0."""
        return (
            dot(weights[:4], (SEP_STATE, pc, _gpow(0), clock)),
            dot(weights[:4], (SEP_MEM, memory_index, memory_ts, memory)),
            dot(weights[:3], (SEP_BYTECODE, bytecode_index, bytecode_count)) + bytecode_value,
            dot(weights[:3], (SEP_RANGE_LO, range_lo_index, range_lo_count)),
            dot(weights[:3], (SEP_RANGE_HI, range_hi_index, range_hi_count)),
        )

    final_pc = _gpow(2**layout.log_bytecode - 1)  # the execution ends at the bytecode's last instruction
    start = fingerprints(_gpow(0), _gpow(CLOCK_STRIDE), ONE, memory_initial, ONE, ONE, ONE)  # cycle 1, every cell at timestamp g^0
    end = fingerprints(final_pc, layout.final_clock, memory_final_ts, memory_final, bytecode_final, range_lo_final, range_hi_final)
    sides = (
        (layout.push, push_layout, start, weights, beta),
        (layout.pull, pull_layout, end, weights, beta),
        (layout.count, count_layout, (), (ONE,), ZERO),  # The count channel owns no framework block and runs at alpha = beta = 0.
    )
    totals = []  # what remains to be proven by the next table sumcheck
    forms = tuple(tuple(Form() for _ in range(3)) for _ in TABLES)
    for side, (blocks, side_layout, framework_fingerprints, side_weights, side_beta) in enumerate(sides):
        framework_selectors = [p.eq_above(point) for p in side_layout.framework]
        table_selectors = [p.eq_above(point) for p in side_layout.tables]
        known = dot(framework_selectors, [side_beta + fingerprint for fingerprint in framework_fingerprints])
        # A table's blocks stay symbolic: they accumulate into the form its sumcheck settles over its own columns.
        beta_form = _const(side_beta)
        for selector, block in zip(table_selectors, blocks, strict=True):
            form = forms[block.owner][side]
            form.add_scaled(beta_form, selector)
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, selector * side_weights[slot])  # the fingerprint, one tuple slot at a time
        # Every occupied row holds beta + its fingerprint; the rest of the leaf cube holds 1.
        ones_padding = E.sum(framework_selectors + table_selectors) + ONE
        totals.append(tree_values[side] + known + ones_padding)  # what the forms owe: the GKR value, less framework and padding

    return BusResult(tuple(claims), point, forms, (totals[0], totals[1], totals[2]))


# Table sumcheck -------------------------------------------------------------


def table_sumcheck(
    table_log_heights: Sequence[int],
    bus_forms: Sequence[Sequence[Form]],
    constraint_powers: Sequence[E],
    form_powers: Sequence[E],
    equality_point: MultilinearPoint,
    target: E,
    transcript: Transcript,
) -> list[ColumnClaim]:
    n_rounds = max(table_log_heights)
    challenges, claim = sumcheck(transcript, target, 4, [None] * n_rounds)
    point = list(reversed(challenges))
    weights = [ONE] * len(TABLES)
    for variable, challenge in enumerate(point):
        equality = ONE + equality_point[variable] + challenge
        for index, height in enumerate(table_log_heights):
            weights[index] *= equality if height > variable else challenge

    final = ZERO
    cursor = 0
    claims: list[ColumnClaim] = []
    for table, height, forms, weight in zip(TABLES, table_log_heights, bus_forms, weights, strict=True):
        evaluations = tuple(transcript.next_scalars(table.width))
        summand = dot(constraint_powers[cursor : cursor + table.n_constraints], table.constraints(evaluations))
        final += weight * (summand + dot(form_powers, [form.evaluate(evaluations.__getitem__) for form in forms]))
        cursor += table.n_constraints
        table_point = tuple(point[:height])
        claims.extend(ColumnClaim(GLOBAL_COLUMN_BASES[table.opcode] + local, table_point, value) for local, value in enumerate(evaluations))
    require(final == claim, "table sumcheck terminal mismatch")
    return claims


R1CS_DIGEST = bytes.fromhex("537ad20790308f8eb8c0e8bd3e6c58ee64573371e3d53c30613dd04d87c0b7ea")

# The columns no instruction table owns. They come first in the global column numbering, the tables after.
NUM_GLOBAL_COLUMNS = 9
MEMORY_INITIAL, MEMORY_FINAL, MEMORY_FINAL_TIMESTAMPS, BYTECODE_FINAL_COUNTERS, RANGE_LO_FINAL_COUNTERS, RANGE_HI_FINAL_COUNTERS, QFLOCK, QADD, QMUL = range(NUM_GLOBAL_COLUMNS)  # fmt: skip

BLAKE2S_R1CS_LOG_SIZE = 14
K_BITS = 64
FLOCK_K_SKIP = log2_ceil(K_BITS)
LOG_PACKING = log2_ceil(K_BITS)  # bits per committed K-element (pcs::pack::LOG_PACKING)

BLAKE2S_CONSTANT_COLUMN = 512
# Flock's zerocheck runs over a cube of at least this many variables: the skip, then seven fixed coordinates.
FLOCK_MIN_LOG_SIZE = 13


@dataclass(frozen=True)
class Layout:
    log_memory: int
    log_bytecode: int
    bytecode: Sequence[K]
    push: tuple[BusBlock, ...]
    pull: tuple[BusBlock, ...]
    count: tuple[BusBlock, ...]
    placements: tuple[Placement, ...]
    stack_log: int
    table_log_heights: tuple[int, ...]
    final_clock: E  # the timestamp the run ended on, announced by the prover


def _cols(columns: Sequence[str], *names: str) -> tuple[int, ...]:
    assert set(names) <= set(columns), f"unknown columns: {sorted(set(names) - set(columns))}"
    return tuple(columns.index(name) for name in names)


def _gpow(index: int) -> E:
    return GEN**index


def _const(value: E | int) -> Form:
    return Form({(): value if isinstance(value, E) else E(value)})


def _col(index: int, exponent: int = 0) -> Form:
    return Form({(index,): _gpow(exponent)})


def _prod(a: int, b: int, exponent: int = 0) -> Form:
    return Form({tuple(sorted((a, b))): _gpow(exponent)})


SEP_STATE = ONE
SEP_MEM = GEN
SEP_BYTECODE = GEN**2
SEP_RANGE_LO = GEN**3
SEP_RANGE_HI = GEN**4

# Memory is read-write, ordered by a clock: access `slot` of cycle `c` carries the timestamp g^(4c + slot).
CLOCK_STRIDE = 4
BLAKE2S_STRIDE = 20  # eighteen accesses, so five cycles' worth of clock
# A gap between two accesses of one cell is range-checked as two 16-bit chunks, each a read of an array of addresses.
RANGE_LOG = 16
RANGE_HI_RATIO = GEN ** -(2**RANGE_LOG)


def _accesses(count: int) -> tuple[str, ...]:
    """The columns of a table's accesses, by kind: the previous timestamps, the gap's two chunks, their read counts."""
    return tuple(f"{kind}_{i}" for kind in ("x", "lo", "hi", "cnt_lo", "cnt_hi") for i in range(count))


class Flushes:
    def __init__(self) -> None:
        self.push: list[tuple[Form, ...]] = []
        self.pull: list[tuple[Form, ...]] = []

    def pair(self, push: Sequence[Form], pull: Sequence[Form]) -> None:
        self.push.append(tuple(push))
        self.pull.append(tuple(pull))

    def state_derived(self, pc: int, fp: int, ts: int, stride: int, npc: Form, nfp: Form) -> None:
        self.pair((_const(SEP_STATE), npc, nfp, _col(ts, stride)), (_const(SEP_STATE), _col(pc), _col(fp), _col(ts)))

    def state_step(self, pc: int, fp: int, ts: int, stride: int = CLOCK_STRIDE) -> None:
        self.state_derived(pc, fp, ts, stride, _col(pc, 1), _col(fp))

    def _counted(self, prefix: Sequence[Form], count: int, suffix: Sequence[Form]) -> None:
        self.pair((*prefix, _col(count, 1), *suffix), (*prefix, _col(count), *suffix))

    def bytecode(self, pc: int, count: int, opcode: int, operands: Sequence[Form]) -> None:
        self._counted((_const(SEP_BYTECODE), _col(pc)), count, (_const(_gpow(opcode)), *operands))

    def memory(self, columns: Sequence[str], address: Form, access: int, slot: int, old: Form, new: Form) -> None:
        """Access `access` of the row, at clock slot `slot`: pull the cell as its previous access left it, push
        it back at this access's timestamp, and read the gap's two chunks off the range arrays."""
        ts, x, lo, hi, cnt_lo, cnt_hi = _cols(columns, "ts", *(f"{kind}_{access}" for kind in ("x", "lo", "hi", "cnt_lo", "cnt_hi")))
        self.pair((_const(SEP_MEM), address, _col(ts, slot), new), (_const(SEP_MEM), address, _col(x), old))
        self._counted((_const(SEP_RANGE_LO), _col(lo)), cnt_lo, ())
        self._counted((_const(SEP_RANGE_HI), _col(hi)), cnt_hi, ())

    def read(self, columns: Sequence[str], address: Form, access: int, slot: int, value: Form) -> None:
        self.memory(columns, address, access, slot, value, value)


def _access_constraints(columns: Sequence[str], slots: Sequence[int]) -> Callable[[Sequence[E]], tuple[E, ...]]:
    """One identity per access, `x * lo = g^slot * ts * hi`: with `lo = g^(d_lo + 1)` and `hi = g^(-2^16 d_hi)`
    read off the range arrays, it says the previous timestamp is `d_lo + 2^16 d_hi + 1` behind this access's own."""
    ts = _cols(columns, "ts")[0]
    triples = [(*_cols(columns, f"x_{i}", f"lo_{i}", f"hi_{i}"), _gpow(slot)) for i, slot in enumerate(slots)]
    return lambda row: tuple(row[x] * row[lo] + shift * row[ts] * row[hi] for x, lo, hi, shift in triples)


# The instruction tables ------------------------------------------------------


@dataclass(frozen=True)
class Table:
    """One instruction's table: its columns, its bus flushes, its constraints."""

    name: str
    opcode: int  # also its index in TABLES, so g^opcode is its bytecode tag
    columns: tuple[str, ...]
    flushes: Flushes
    constraints: Callable[[Sequence[E]], tuple[E, ...]] = lambda _: ()

    @property
    def n_constraints(self) -> int:
        return len(self.constraints([ZERO] * self.width))

    @property
    def width(self) -> int:
        return len(self.columns)

    @property
    def count_columns(self) -> tuple[int, ...]:
        return tuple(i for i, name in enumerate(self.columns) if name.startswith("cnt"))


def _flushes_arith64(opcode: int, multiply: bool) -> Flushes:
    pc, fp, o_a, o_b, o_c, va, vb, vc_old, ts, cnt_bc = _cols(ARITH64_COLUMNS, "pc", "fp", "o_a", "o_b", "o_c", "va", "vb", "vc_old", "ts", "cnt_bc")
    flushes = Flushes()
    flushes.state_step(pc, fp, ts)
    flushes.bytecode(pc, cnt_bc, opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    flushes.read(ARITH64_COLUMNS, _prod(fp, o_a), 0, 0, _col(va))
    flushes.read(ARITH64_COLUMNS, _prod(fp, o_b), 1, 1, _col(vb))
    flushes.memory(ARITH64_COLUMNS, _prod(fp, o_c), 2, 2, _col(vc_old), _prod(va, vb) if multiply else _col(va) + _col(vb))
    return flushes


def _flushes_u64(opcode: int) -> Flushes:
    """`ADD_U64` and `MUL_U64`: the result is a column of its own, tied to the operands by flock, not by a form."""
    pc, fp, o_a, o_b, o_c, va, vb, vc, vc_old, ts, cnt_bc = _cols(
        U64_COLUMNS, "pc", "fp", "o_a", "o_b", "o_c", "va", "vb", "vc", "vc_old", "ts", "cnt_bc"
    )
    flushes = Flushes()
    flushes.state_step(pc, fp, ts)
    flushes.bytecode(pc, cnt_bc, opcode, (_col(o_a), _col(o_b), _col(o_c), _const(ZERO), _const(ZERO)))
    flushes.read(U64_COLUMNS, _prod(fp, o_a), 0, 0, _col(va))
    flushes.read(U64_COLUMNS, _prod(fp, o_b), 1, 1, _col(vb))
    flushes.memory(U64_COLUMNS, _prod(fp, o_c), 2, 2, _col(vc_old), _col(vc))
    return flushes


def _flushes_set() -> Flushes:
    pc, fp, o, k, v_old, ts, cnt_bc = _cols(SET_COLUMNS, "pc", "fp", "o", "k", "v_old", "ts", "cnt_bc")
    flushes = Flushes()
    flushes.state_step(pc, fp, ts)
    flushes.bytecode(pc, cnt_bc, OP_SET, (_col(o), _col(k), _const(ZERO), _const(ZERO), _const(ZERO)))
    flushes.memory(SET_COLUMNS, _prod(fp, o), 0, 0, _col(v_old), _col(k))
    return flushes


def _flushes_deref() -> Flushes:
    pc, fp, o1, o2, o3, f_pc, f_fp, ptr, v3 = _cols(DEREF_COLUMNS, "pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3")
    v2_old, ts, cnt_bc = _cols(DEREF_COLUMNS, "v2_old", "ts", "cnt_bc")
    # v2 = (1 + f_pc + f_fp)*v3 + f_pc*(g^2*pc) + f_fp*fp
    store = Form.sum((_col(v3), _prod(f_pc, v3), _prod(f_fp, v3), _prod(f_pc, pc, 2), _prod(f_fp, fp)))
    flushes = Flushes()
    flushes.state_step(pc, fp, ts)
    flushes.bytecode(pc, cnt_bc, OP_DEREF, (_col(o1), _col(o2), _col(o3), _col(f_pc), _col(f_fp)))
    # The pointer and the local cell are read before the target is written.
    flushes.read(DEREF_COLUMNS, _prod(fp, o1), 0, 0, _col(ptr))
    flushes.read(DEREF_COLUMNS, _prod(fp, o3), 1, 1, _col(v3))
    flushes.memory(DEREF_COLUMNS, _prod(ptr, o2), 2, 2, _col(v2_old), store)
    return flushes


def _flushes_jump() -> Flushes:
    pc, fp, o_c, o_d, o_f, cond, dest, frame, b = _cols(JUMP_COLUMNS, "pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "b")
    ts, cnt_bc = _cols(JUMP_COLUMNS, "ts", "cnt_bc")
    flushes = Flushes()
    # next_pc = b*dest + (b+1)*g*pc, next_fp = b*frame + (b+1)*fp, both derived.
    flushes.state_derived(pc, fp, ts, CLOCK_STRIDE, _prod(b, dest) + _prod(b, pc, 1) + _col(pc, 1), _prod(b, frame) + _prod(b, fp) + _col(fp))
    flushes.bytecode(pc, cnt_bc, OP_JUMP, (_col(o_c), _col(o_d), _col(o_f), _const(ZERO), _const(ZERO)))
    flushes.read(JUMP_COLUMNS, _prod(fp, o_c), 0, 0, _col(cond))
    flushes.read(JUMP_COLUMNS, _prod(fp, o_d), 1, 1, _col(dest))
    flushes.read(JUMP_COLUMNS, _prod(fp, o_f), 2, 2, _col(frame))
    return flushes


def _jump_constraints(columns: Sequence[E]) -> tuple[E, ...]:
    condition, inverse, flag = (columns[index] for index in _cols(JUMP_COLUMNS, "v_cond", "w", "b"))
    return (flag + condition * inverse, condition * (flag + ONE), *_access_constraints(JUMP_COLUMNS, (0, 1, 2))(columns))


def _flushes_blake2s() -> Flushes:
    pc, fp, ts, cnt_bc = _cols(BLAKE2S_COLUMNS, "pc", "fp", "ts", "cnt_bc")
    operands = _cols(BLAKE2S_COLUMNS, "o_0", "o_1", "o_2", "o_3", "o_cv", "o_out", "o_md")
    flushes = Flushes()
    flushes.state_step(pc, fp, ts, BLAKE2S_STRIDE)
    flushes.bytecode(pc, cnt_bc, OP_BLAKE2S, tuple(_col(i) for i in operands))
    for access, (lane, operand, exponent, slot) in enumerate(BLAKE2S_LANES):
        value, address = _cols(BLAKE2S_COLUMNS, lane, operand)
        # The digest lanes are writes: what the cell held before is its own column.
        old = _cols(BLAKE2S_COLUMNS, f"{lane}_old")[0] if lane.startswith("out") else value
        flushes.memory(BLAKE2S_COLUMNS, _prod(fp, address, exponent), access, slot, _col(old), _col(value))
    return flushes


OP_XOR64, OP_MUL64, OP_SET, OP_DEREF, OP_JUMP, OP_BLAKE2S, OP_ADD_U64, OP_MUL_U64 = range(8)

# A write's destination carries what the cell held before (`*_old`); every access carries its `_accesses` columns.
ARITH64_COLUMNS = ("pc", "fp", "o_a", "o_b", "o_c", "va", "vb", "vc_old", "ts", *_accesses(3), "cnt_bc")
SET_COLUMNS = ("pc", "fp", "o", "k", "v_old", "ts", *_accesses(1), "cnt_bc")
# The two operands and the result live in the operation's flock witness, like BLAKE2s's lanes in q_flock.
U64_COLUMNS = ("pc", "fp", "o_a", "o_b", "o_c", "va", "vb", "vc", "vc_old", "ts", *_accesses(3), "cnt_bc")
DEREF_COLUMNS = ("pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3", "v2_old", "ts", *_accesses(3), "cnt_bc")
JUMP_COLUMNS = ("pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "ts", "w", "b", *_accesses(3), "cnt_bc")
# The eighteen cells a BLAKE2s row touches, as (value lane, operand, offset from it, clock slot): each message chunk's two
# cells, then the digest's four, the chaining value's four and the metadata's two (the byte counter, then the flags).
# The fourteen reads take the first slots and the four digest writes the last, so a digest may land on a cell the row read.
BLAKE2S_LANES = (
    ("m0_lo", "o_0", 0, 0), ("m0_hi", "o_0", 1, 1), ("m1_lo", "o_1", 0, 2), ("m1_hi", "o_1", 1, 3),
    ("m2_lo", "o_2", 0, 4), ("m2_hi", "o_2", 1, 5), ("m3_lo", "o_3", 0, 6), ("m3_hi", "o_3", 1, 7),
    ("out0", "o_out", 0, 14), ("out1", "o_out", 1, 15), ("out2", "o_out", 2, 16), ("out3", "o_out", 3, 17),
    ("cv0", "o_cv", 0, 8), ("cv1", "o_cv", 1, 9), ("cv2", "o_cv", 2, 10), ("cv3", "o_cv", 3, 11),
    ("md_lo", "o_md", 0, 12), ("md_hi", "o_md", 1, 13),
)  # fmt: skip
BLAKE2S_COLUMNS = (
    "pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_cv", "o_out", "o_md",
    # The value lanes live in q_flock, not here: each is already a flock witness slot.
    *(lane for lane, _, _, _ in BLAKE2S_LANES),
    "out0_old", "out1_old", "out2_old", "out3_old", "ts", *_accesses(len(BLAKE2S_LANES)), "cnt_bc",
)  # fmt: skip

TABLES = (
    Table("xor64", OP_XOR64, ARITH64_COLUMNS, _flushes_arith64(OP_XOR64, multiply=False), _access_constraints(ARITH64_COLUMNS, (0, 1, 2))),
    Table("mul64", OP_MUL64, ARITH64_COLUMNS, _flushes_arith64(OP_MUL64, multiply=True), _access_constraints(ARITH64_COLUMNS, (0, 1, 2))),
    Table("set", OP_SET, SET_COLUMNS, _flushes_set(), _access_constraints(SET_COLUMNS, (0,))),
    Table("deref", OP_DEREF, DEREF_COLUMNS, _flushes_deref(), _access_constraints(DEREF_COLUMNS, (0, 1, 2))),
    Table("jump", OP_JUMP, JUMP_COLUMNS, _flushes_jump(), _jump_constraints),
    Table(
        "blake2s", OP_BLAKE2S, BLAKE2S_COLUMNS, _flushes_blake2s(), _access_constraints(BLAKE2S_COLUMNS, [slot for _, _, _, slot in BLAKE2S_LANES])
    ),
    Table("add_u64", OP_ADD_U64, U64_COLUMNS, _flushes_u64(OP_ADD_U64), _access_constraints(U64_COLUMNS, (0, 1, 2))),
    Table("mul_u64", OP_MUL_U64, U64_COLUMNS, _flushes_u64(OP_MUL_U64), _access_constraints(U64_COLUMNS, (0, 1, 2))),
)

# Where in the flock witness each BLAKE2s value lane lives: one 64-bit slot per lane, the chaining value first, then the
# digest, the message block and the metadata. Slots 8 and 9 are flock's constant wire and the padding up to its message base, which no memory cell carries.
BLAKE2S_SLOTS = (
    "cv0", "cv1", "cv2", "cv3", "out0", "out1", "out2", "out3", None, None,
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi", "md_lo", "md_hi",
)  # fmt: skip


@dataclass(frozen=True)
class FlockWitness:
    """One circuit's packed witness, a committed column: instance j is row j of the circuit's table, and the
    table's value columns are whole packed words of it, so they are committed there and nowhere else."""

    column: int
    table: int
    log_size: int  # log2 of the bits one instance occupies
    slots: tuple[str | None, ...]  # the table column held by each of the instance's leading packed words

    @property
    def slot_bits(self) -> int:
        return self.log_size - LOG_PACKING

    @property
    def min_log_height(self) -> int:
        """A batch is at least eight instances, and the zerocheck's cube at least 2^13 bits."""
        return max(3, FLOCK_MIN_LOG_SIZE - self.log_size)


U64_SLOTS = ("va", "vb", "vc")
FLOCK_WITNESSES = (
    FlockWitness(QFLOCK, OP_BLAKE2S, BLAKE2S_R1CS_LOG_SIZE, BLAKE2S_SLOTS),
    FlockWitness(QADD, OP_ADD_U64, 8, U64_SLOTS),
    FlockWitness(QMUL, OP_MUL_U64, 12, U64_SLOTS),
)

TABLE_WIDTHS = tuple(t.width for t in TABLES)
GLOBAL_COLUMN_BASES = tuple(NUM_GLOBAL_COLUMNS + sum(TABLE_WIDTHS[:table]) for table in range(len(TABLES)))


def build_layout(bytecode: Sequence[K], log_memory: int, table_log_heights: Sequence[int], final_clock: E) -> Layout:
    log_bytecode = log2_strict(len(bytecode)) - BUS_BITS
    require(
        16 <= log_memory <= 32
        and all(0 <= log_height <= 32 for log_height in table_log_heights)
        and all(table_log_heights[witness.table] >= witness.min_log_height for witness in FLOCK_WITNESSES)
        and 0 <= log_bytecode <= 32,
        "invalid announced table sizes",
    )

    push: list[BusBlock] = []
    pull: list[BusBlock] = []
    count: list[BusBlock] = []
    for table, height in zip(TABLES, table_log_heights, strict=True):
        flushes = table.flushes
        for coordinates in flushes.push:
            push.append(BusBlock(height, coordinates, table.opcode))
        for coordinates in flushes.pull:
            pull.append(BusBlock(height, coordinates, table.opcode))
        for local in table.count_columns:
            count.append(BusBlock(height, (_col(local),), table.opcode))

    # Every column's log size, in global order: the framework's, the flock witnesses', then each table's block.
    flock_kappas = [table_log_heights[witness.table] + witness.slot_bits for witness in FLOCK_WITNESSES]
    kappas = [log_memory, log_memory, log_memory, log_bytecode, RANGE_LOG, RANGE_LOG, *flock_kappas]
    for table in TABLES:
        kappas += [table_log_heights[table.opcode]] * table.width

    # A flock-backed value column gets no block of its own: it is committed inside its circuit's witness, whose
    # slots interleave, so it sits at that witness's offset behind its own slot's bits. Same width either way.
    limbs = {
        GLOBAL_COLUMN_BASES[witness.table] + _cols(TABLES[witness.table].columns, name)[0]: (witness, slot)
        for witness in FLOCK_WITNESSES
        for slot, name in enumerate(witness.slots)
        if name
    }
    blocks = {column: kappa for column, kappa in enumerate(kappas) if column not in limbs}
    block_offsets, total_log = stack_offsets(list(blocks.values()))
    offsets = dict(zip(blocks, block_offsets))
    stack_log = max(MIN_STACKED_LOG, total_log)  # Floor at the PCS minimum

    def placement(column: int, kappa: int) -> Placement:
        if column not in limbs:
            return Placement(kappa, offsets[column])
        witness, slot = limbs[column]
        return Placement(kappa, offsets[witness.column] + slot, witness.slot_bits)

    placements = [placement(column, kappa) for column, kappa in enumerate(kappas)]
    return Layout(
        log_memory,
        log_bytecode,
        bytecode,
        tuple(push),
        tuple(pull),
        tuple(count),
        tuple(placements),
        stack_log,
        tuple(table_log_heights),
        final_clock,
    )


# WHIR opening ----------------------------------------------------------------

INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 4
RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 3
RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR = 1
RESIDUAL_MAX_LOG = 5
QUERY_GRINDING_BITS = 17

MIN_STACKED_LOG = 15
MAX_STACKED_LOG = 28

WHIR_QUERIES = (((223,55), (223,56,30), (223,56,31), (224,56,32), (224,56,32), (224,56,32,22), (224,56,32,22), (225,56,32,23), (225,56,32,23), (225,56,32,23,17), (226,56,32,23,17), (226,56,32,23,18), (227,56,32,23,18), (228,56,32,23,18,14)), ((112,45), (112,45,27), (112,45,28), (112,45,28), (112,45,28), (112,45,28,20), (112,45,28,20), (112,45,28,21), (112,45,28,21), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,17,13)), ((75,37), (75,37,24), (75,38,25), (75,38,25), (75,38,25), (75,38,25,18), (75,38,25,19), (75,38,25,19), (75,38,25,19), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (76,38,25,19,16,13)), ((56,32), (56,32,22), (56,32,22), (56,32,23), (56,32,23), (56,32,23,17), (56,32,23,17), (56,32,23,18), (56,32,23,18), (57,32,23,18,14), (57,32,23,18,14), (57,32,23,18,15), (57,33,23,18,15), (57,33,23,18,15,12)))  # fmt: skip


@dataclass(frozen=True)
class WhirConfig:
    log_inv_rates: tuple[int, ...]
    folds: tuple[int, ...]
    queries: tuple[int, ...]


def derive_config(log_n: int, log_inv_rate: int) -> WhirConfig:
    """The opening shape at this size and rate: the ladder geometry, then the
    tabulated query counts."""
    require(MIN_STACKED_LOG <= log_n <= MAX_STACKED_LOG and 1 <= log_inv_rate <= 4, "invalid WHIR shape")
    folds = [INITIAL_FOLDING_FACTOR]
    log_inv_rates = [log_inv_rate]
    remaining = log_n - INITIAL_FOLDING_FACTOR
    while remaining > RESIDUAL_MAX_LOG:
        first = len(folds) == 1
        log_inv_rates.append(log_inv_rates[-1] + folds[-1] - (RS_DOMAIN_INITIAL_REDUCTION_FACTOR if first else RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR))
        fold = min(SUBSEQUENT_FOLDING_FACTOR, remaining)
        remaining -= fold
        folds.append(fold)
    queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG]
    require(len(queries) == len(folds), "tabulated query count does not match the ladder")
    return WhirConfig(log_inv_rates=tuple(log_inv_rates), folds=tuple(folds), queries=queries)


def _ext_row(words: Sequence[K]) -> tuple[E, ...]:
    """Regroup a level's leaf words into the E values they encode, three per lane."""
    return tuple(E(*words[i : i + 3]) for i in range(0, len(words), 3))


def sample_queries(transcript: Transcript, block_length: int, count: int) -> list[int]:
    depth = log2_strict(block_length)
    per_word = 192 // depth
    result: list[int] = []
    while len(result) < count:
        bits = int(transcript.sample())
        for chunk in range(min(per_word, count - len(result))):
            result.append((bits >> (chunk * depth)) & (block_length - 1))
    return result


def _enforced_sum(rows: Sequence[Sequence[K | E]], folds: Sequence[E], query_weights: Sequence[E]) -> E:
    lane_weights = eq_kernel(folds)
    total = ZERO
    for query_weight, row in zip(query_weights, rows, strict=True):
        total += query_weight * dot(row, lane_weights)
    return total


def _subspace_roots(log_n: int) -> list[E]:
    roots = [ONE]
    layer = [E(2**i) for i in range(1, log_n + 1)]
    for _ in range(log_n):
        layer = [value**2 + roots[-1] * value for value in layer]
        roots.append(layer.pop(0))
    return roots


def _induced_weight(message_log: int, queries: Sequence[int], query_weights: Sequence[E], point: Sequence[E]) -> E:
    """The level's batched query claims, as one weight at `point`.

    Each query contributes the novel-basis column weight of doc annex B, Lemma
    lem:colweight, `prod_k (1 + p_k (1 + W-hat_k(x_q)))`, scaled by its power of
    the level's batching challenge.
    """
    require(len(point) == message_log, "bad induced-basis dimensions")
    roots = _subspace_roots(message_log)
    inverses = [value.inv() if value else ZERO for value in roots]
    total = ZERO
    for weight, query in zip(query_weights, queries, strict=True):
        basis = E(query)
        product = weight
        for coordinate, challenge in enumerate(point):
            product *= ONE + challenge * (ONE + basis * inverses[coordinate])
            basis = basis**2 + roots[coordinate] * basis
        total += product
    return total


@dataclass(frozen=True)
class GluedClaim:
    """One claim folded into the running sumcheck, and the weight it owes back.

    A level's batched queries and an out-of-domain claim differ only in that
    weight: both are a power of the level's lambda times a function of the
    terminal point, restricted to the level's own message coordinates.
    """

    scalar: E  # the power of lambda it was glued with
    fold_start: int  # how many fold challenges preceded the level
    weight_at: Callable[[Sequence[E]], E]


def verify_whir(transcript: Transcript, log_n: int, log_inv_rate: int, target: E, root: Digest, evaluate_basis: Callable[[Sequence[E]], E]) -> None:
    """Verify the base-field multilevel opening with a one-point terminal check."""
    config = derive_config(log_n, log_inv_rate)
    levels = len(config.folds)

    running_quad = transcript.sumcheck_round_poly(3, target)
    folds: list[E] = []
    glued: list[GluedClaim] = []
    current_root = root

    for level, (fold_count, level_rate) in enumerate(zip(config.folds, config.log_inv_rates, strict=True)):
        level_folds: list[E] = []
        for _ in range(fold_count):
            challenge = transcript.sample()
            folds.append(challenge)
            level_folds.append(challenge)
            running_quad = transcript.sumcheck_round_poly(3, poly_eval(running_quad, challenge))

        message_log = log_n - len(folds)
        final_level = level == levels - 1
        # The level's claims, held until its batching challenge is drawn: the
        # OOD claims first, then the query batch (Annex B, Protocol 1 step 1).
        pending: list[tuple[Sequence[E], Callable[[Sequence[E]], E]]] = []
        if final_level:
            residual = tuple(transcript.next_scalars(2**message_log))
        else:
            next_root = Digest.from_halves(*transcript.next_scalars(2))
            ood_point = tuple(transcript.samples(message_log))
            ood_value = transcript.next_scalar()
            pending.append((transcript.sumcheck_round_poly(3, ood_value), lambda x, z=ood_point: eq_eval(z, x)))

        transcript.grind_check(QUERY_GRINDING_BITS)
        block_length = 2 ** (message_log + level_rate)
        queries = sample_queries(transcript, block_length, config.queries[level])
        # One batching challenge per level, drawn once every claim it batches is
        # fixed: the OOD claims above and these query positions.
        lam = transcript.sample()
        query_weights = powers(lam, len(queries))
        # Level 0 committed the K witness, one leaf word per lane; every deeper
        # level a folded E one, three words per lane.
        lanes = 2**fold_count
        words = transcript.merkle(current_root, block_length, queries, lanes if level == 0 else 3 * lanes)
        rows: list[Sequence[K | E]] = [tuple(reversed(row)) for row in words] if level == 0 else [_ext_row(row) for row in words]
        enforced = _enforced_sum(rows, level_folds, query_weights)

        # Every commitment, including the last one, enters through an intro
        # message; the level's claims are then batched with powers of `lam`,
        # the running claim keeping lam^0 = 1.
        batch = (message_log, tuple(queries), tuple(query_weights))
        pending.append((transcript.sumcheck_round_poly(3, enforced), lambda x, b=batch: _induced_weight(*b, x)))
        scalar = ONE
        for intro, weight_at in pending:
            scalar *= lam
            running_quad = [q + scalar * i for q, i in zip(running_quad, intro, strict=True)]
            glued.append(GluedClaim(scalar, len(folds), weight_at))

        if final_level:
            # Finish the remaining sumcheck rounds and close on one evaluation
            # of every basis at the resulting point.
            tail_folds: list[E] = []
            for round_index in range(message_log):
                challenge = transcript.sample()
                running_target = poly_eval(running_quad, challenge)
                tail_folds.append(challenge)
                if round_index + 1 < message_log:
                    running_quad = transcript.sumcheck_round_poly(3, running_target)
            # Each glued claim is rebound at the terminal point: the fold
            # challenges its level fixed after it was made, then the tail.
            point = folds + tail_folds
            lane_folds = config.folds[0]
            weight = evaluate_basis(point[lane_folds:] + point[:lane_folds])
            for claim in glued:
                weight += claim.scalar * claim.weight_at(folds[claim.fold_start :] + tail_folds)
            terminal = weight * multilinear_eval(residual, tail_folds)
            require(terminal == running_target, "WHIR terminal check failed")
            return
        current_root = next_root

    raise VerificationError("WHIR verification ended without a terminal level")


# Flock reduction -------------------------------------------------------------

PHI_BASIS = (E(0x0000000000000001), E(0x033CE8BEDDC8A656), E(0x512620375ED2A108), E(0x0C9E636090AAFC01), E(0xBA4F3CD82801769C), E(0xBA26E7904ADB4A47), E(0x467698598926DC01), E(0x4418AE808B28BDD0))  # fmt: skip
PHI = tuple(E.sum(PHI_BASIS[bit] for bit in range(8) if value >> bit & 1) for value in range(256))

_MEDIUM_GENERATOR = E(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0)

FIXED_CHALLENGES = (
    PHI[0xF7], PHI[0x53], PHI[0xB5],
    *tuple(_MEDIUM_GENERATOR ** (2**power) / (ONE + _MEDIUM_GENERATOR ** (2**power)) for power in range(4)),
)  # fmt: skip


@cache
def _window_denominator(count: int) -> E:
    """The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.

    PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
    `j -> i ^ j` only permutes the block. Every node is left the same product.
    """
    return reduce(mul, PHI[1:count], ONE).inv()


def lagrange_weights(count: int, point: E) -> list[E]:
    """The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products."""
    differences = [point + node for node in PHI[:count]]
    prefix = list(accumulate(differences, mul, initial=ONE))
    suffix = list(accumulate(reversed(differences), mul, initial=ONE))[::-1]
    denominator = _window_denominator(count)
    return [p * s * denominator for p, s in zip(prefix[:count], suffix[1:])]


def lagrange_interpolate(count: int, values: Sequence[E], point: E) -> E:
    return dot(lagrange_weights(count, point), values)


@dataclass(frozen=True)
class ZerocheckResult:
    z_skip: E
    chi: MultilinearPoint
    v_a: E
    v_b: E
    v_c: E


def verify_flock_zerocheck(log_n: int, transcript: Transcript) -> ZerocheckResult:
    """The zerocheck: one univariate skip round, then nflock quadratic ones.
    C rides those rounds with AB, so all three claims come out at one point."""
    # The point r: seven fixed coordinates, the rest sampled.
    r = (*FIXED_CHALLENGES, *transcript.samples(log_n - FLOCK_K_SKIP - len(FIXED_CHALLENGES)))

    # P = P^AB + P^C on the coset, then z_skip; the 64 zeros on Lambda are assumed.
    p_coset = transcript.next_scalars(K_BITS)
    z_skip = transcript.sample()
    v_p = lagrange_interpolate(2 * K_BITS, [ZERO] * K_BITS + list(p_coset), z_skip)

    # nflock quadratic rounds on P, closed by v_a, v_b.
    chi, running = sumcheck(transcript, v_p, 3, r)
    v_a, v_b = transcript.next_scalars(2)
    v_c = running + v_a * v_b
    return ZerocheckResult(z_skip, chi, v_a, v_b, v_c)


@dataclass(frozen=True)
class FlockCircuit:
    """What the reduction needs of a circuit: its block size, where its constant wire sits, and the walk that
    evaluates `e_row^T (A0 + alpha B0) w_col` without building either matrix."""

    log_size: int
    constant_column: int
    bilinear: Callable[[E, Sequence[E], Sequence[E]], E]


def verify_flock_lincheck(circuit: FlockCircuit, zc: ZerocheckResult, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """Lincheck at the quirky point (z_skip, chi): the claim's point, then its 64 slices s."""
    n_rounds = circuit.log_size - FLOCK_K_SKIP
    alpha = transcript.sample()  # batches the two matrix identities, the c claim and the constant-position claim
    # e_row: phi8 Lagrange in the skip coordinate, eq in the slot variables.
    skip_weights = lagrange_weights(K_BITS, zc.z_skip)
    chi_in = zc.chi[:n_rounds]
    e_row = [weight * value for weight in eq_kernel(chi_in) for value in skip_weights]

    # The rounds that bind the high column coordinates (8 for BLAKE2s), leaving 64 unfolded.
    claim = zc.v_a + alpha * zc.v_b + alpha**2 * zc.v_c + alpha**3
    round_challenges, r_lc = sumcheck(transcript, claim, 3, [None] * n_rounds)

    # The residual, then the terminal identity: pin term and c term included.
    # C = I, so the c weight is e_row itself, and both sides being tensors it
    # collapses to eq(chi_in, chi_in_prime) times a 64-term Lagrange combination.
    s = tuple(transcript.next_scalars(K_BITS))
    chi_in_prime = tuple(reversed(round_challenges))
    w_col = [value * weight for weight in eq_kernel(chi_in_prime) for value in s]
    terminal = (
        circuit.bilinear(alpha, e_row, w_col)
        + alpha**2 * eq_eval(chi_in, chi_in_prime) * dot(skip_weights, s)
        + alpha**3 * w_col[circuit.constant_column]
    )
    require(terminal == r_lc, "Flock lincheck terminal mismatch")
    return chi_in_prime + zc.chi[n_rounds:], s


def blake2s_row_values(column_weights: Sequence[E]) -> tuple[list[E], list[E]]:
    """Compute `A0 w` and `B0 w` by one forward walk of the circuit."""
    size = 2**BLAKE2S_R1CS_LOG_SIZE
    constant = BLAKE2S_CONSTANT_COLUMN
    message_base = 640
    counter_low = 1152
    counter_high = 1184
    final_flag = 1216
    last_node_flag = 1248
    gates_base = 1280
    gate_stride = 184
    left_values = [ZERO] * size
    right_values = [ZERO] * size

    def slots(base: int) -> tuple[E, ...]:
        return tuple(column_weights[base + bit] for bit in range(32))

    def literal(value: int) -> tuple[E, ...]:
        return tuple(column_weights[constant] if value >> bit & 1 else ZERO for bit in range(32))

    def xor(x: Sequence[E], y: Sequence[E]) -> tuple[E, ...]:
        return tuple(a + b for a, b in zip(x, y, strict=True))

    def rotate_right(word: Sequence[E], amount: int) -> tuple[E, ...]:
        return tuple(word[(bit + amount) & 31] for bit in range(32))

    def add(x: Sequence[E], y: Sequence[E], carry_base: int) -> tuple[E, ...]:
        carry = ZERO
        output = []
        for bit in range(32):
            if bit < 31:
                left_values[carry_base + bit] = x[bit] + carry
                right_values[carry_base + bit] = y[bit] + carry
            output.append(x[bit] + y[bit] + carry)
            if bit < 31:
                carry += column_weights[carry_base + bit]
        return tuple(output)

    def add3(x: Sequence[E], y: Sequence[E], z: Sequence[E], base: int) -> tuple[E, ...]:
        """Fused three-operand add: 31 majority rows then 30 ripple rows.

        The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
        `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
        `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
        ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
        bit `i`.
        """
        majority = []
        for bit in range(31):
            left_values[base + bit] = x[bit] + z[bit]
            right_values[base + bit] = y[bit] + z[bit]
            majority.append(column_weights[base + bit] + z[bit])
        ripple_base = base + 31
        carry = ZERO
        output = []
        for bit in range(32):
            q = ZERO if bit == 0 else majority[bit - 1]
            left = x[bit] + y[bit] + z[bit] + carry
            output.append(left + q)
            if 1 <= bit <= 30:
                left_values[ripple_base + bit - 1] = left
                right_values[ripple_base + bit - 1] = q + carry
                carry += column_weights[ripple_base + bit - 1]
        return tuple(output)

    def linear_rows(values: Sequence[E], base: int) -> None:
        for bit in range(32):
            left_values[base + bit] = values[bit]
            right_values[base + bit] = column_weights[constant]

    for base, length in ((0, 256), (message_base, 512), (counter_low, 128)):
        for row in range(base, base + length):
            left_values[row] = column_weights[row]
            right_values[row] = column_weights[constant]

    # v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    state = [slots(32 * word) for word in range(8)]
    state.extend(literal(BLAKE2S_IV[word]) for word in range(4))
    state.extend(xor(literal(BLAKE2S_IV[4 + word]), slots(base)) for word, base in enumerate((counter_low, counter_high, final_flag, last_node_flag)))

    for round_index in range(10):
        sigma = BLAKE2S_SIGMA[round_index]
        for gate_index, (lane_a, lane_b, lane_c, lane_d) in enumerate(BLAKE2S_G_LANES):
            gate = round_index * 8 + gate_index
            gate_base = gates_base + gate_stride * gate
            a, b, c, d = state[lane_a], state[lane_b], state[lane_c], state[lane_d]
            mx = slots(message_base + 32 * sigma[2 * gate_index])
            my = slots(message_base + 32 * sigma[2 * gate_index + 1])
            a1 = add3(a, b, mx, gate_base)
            d1 = rotate_right(xor(d, a1), 16)
            c1 = add(c, d1, gate_base + 61)
            b1 = rotate_right(xor(b, c1), 12)
            a2 = add3(a1, b1, my, gate_base + 92)
            d2 = rotate_right(xor(d1, a2), 8)
            c2 = add(c1, d2, gate_base + 153)
            b2 = rotate_right(xor(b1, c2), 7)
            # Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2
            state[lane_b] = b2
            state[lane_c] = c2
            state[lane_d] = d2

    # out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in range(8):
        out = xor(xor(state[word], state[word + 8]), slots(32 * word))
        linear_rows(out, 256 + 32 * word)

    left_values[constant] = column_weights[constant]
    right_values[constant] = column_weights[constant]
    return left_values, right_values


def blake2s_bilinear(alpha: E, row_weights: Sequence[E], column_weights: Sequence[E]) -> E:
    """Compute `e_row^T (A0 + alpha B0) w_col` from the two forward row vectors."""
    left_values, right_values = blake2s_row_values(column_weights)
    return dot(row_weights, left_values) + alpha * dot(row_weights, right_values)


# The u64 circuits ------------------------------------------------------------
#
# One instance is `a` in bits [0, 64), `b` in [64, 128), the result in [128, 192), the constant wire at 192, then
# the circuit's products. A circuit is a gate list, a wire being the gate that drives it: a free committed wire
# (an input or the constant), an uncommitted XOR, an AND whose product is committed at a slot, or a copy that
# commits an affine wire at a slot, which is how the result leaves.

type Gate = tuple[str, int, int, int]
U64_CONSTANT_COLUMN = 192


class _GateList:
    def __init__(self) -> None:
        self.gates: list[Gate] = []
        self.next_slot = U64_CONSTANT_COLUMN + 1
        self.one = self.push("free", U64_CONSTANT_COLUMN)
        self.a = [self.push("free", i) for i in range(64)]
        self.b = [self.push("free", 64 + i) for i in range(64)]

    def push(self, kind: str, x: int, y: int = 0, slot: int = 0) -> int:
        self.gates.append((kind, x, y, slot))
        return len(self.gates) - 1

    def xor(self, x: int | None, y: int | None) -> int | None:
        """`None` is a structural zero."""
        if x is None or y is None:
            return y if x is None else x
        return self.push("xor", x, y)

    def product(self, x: int | None, y: int | None) -> int:
        assert x is not None and y is not None
        self.next_slot += 1
        return self.push("and", x, y, self.next_slot - 1)

    def output(self, position: int, wire: int | None) -> None:
        assert wire is not None, "every result bit has a wire"
        self.push("copy", wire, 0, 128 + position)

    def ripple_carry(self, x: Sequence[int | None], y: Sequence[int | None]) -> None:
        """Commit `x + y mod 2^64`: a carry is `maj(x, y, c) = (x ^ c)(y ^ c) ^ c`, one product, wherever two
        of the three are present, and the carry out of the top bit falls off the modulus."""
        carry = None
        for position, (wx, wy) in enumerate(zip(x, y, strict=True)):
            if position < 63 and sum(wire is not None for wire in (wx, wy, carry)) >= 2:
                xc, yc = self.xor(wx, carry), self.xor(wy, carry)
                carry = self.xor(self.product(xc, yc), carry)
                out = self.xor(xc, wy)
            else:
                out, carry = self.xor(self.xor(wx, wy), carry), None
            self.output(position, out)


def _adder() -> _GateList:
    """Wrapping addition: a ripple-carry adder, 63 products."""
    c = _GateList()
    carry = None
    for i in range(64):
        ac, bc = c.xor(c.a[i], carry), c.xor(c.b[i], carry)
        c.output(i, c.xor(ac, c.b[i]))
        if i < 63:
            carry = c.xor(c.product(ac, bc), carry)
    return c


def _multiplier() -> _GateList:
    """Wrapping multiplication. With `e_ij = not(a_i ^ b_j)`, `2 a_i b_j = a_i + b_j - 1 + e_ij`, so twice the product
    is a sum of 66 rows of affine bits: `(a_i ? b : not b) << i`, then `not a + a 2^64` and the same for `b`.
    Its column 0 is `2 + 2g` with `g = (not a_0)(not b_0)`, so after that one product the identity halves, `1` and `g`
    taking the empty low bits of two rows. Carry-save steps then compress three rows into two, the three ending
    lowest each time, and a ripple-carry addition finishes. Every product is a majority."""
    c = _GateList()
    n = 64
    width = (1 << n) - 1
    not_a = [c.xor(wire, c.one) for wire in c.a]
    not_b = [c.xor(wire, c.one) for wire in c.b]
    g = c.product(not_a[0], not_b[0])

    rows: list[list[int | None]] = [[None] * n for _ in range(66)]
    for i in range(64):
        for j in range(64):
            if 0 <= i + j - 1 < n:
                rows[i][i + j - 1] = c.xor(c.b[j], not_a[i])
    for row, low, high in ((64, not_a, c.a), (65, not_b, c.b)):
        rows[row][:63] = low[1:]
        rows[row][63] = high[0]
    rows[2][0], rows[3][0] = c.one, g
    present = [sum(1 << p for p in range(n) if row[p] is not None) for row in rows]

    live = list(range(66))
    while len(live) > 2:
        # The three rows ending lowest: by highest position, then by lowest, ties in `live` order.
        order = sorted(range(len(live)), key=lambda t: (present[live[t]].bit_length(), (present[live[t]] & -present[live[t]]).bit_length()))
        x, y, z = (live[t] for t in order[:3])
        live = [row for row in live if row not in (x, y, z)] + [x, y]
        px, py, pz = present[x], present[y], present[z]
        pairs = ((px & py) | (px & pz) | (py & pz)) & (width >> 1)
        triples = px & py & pz
        products = moves = 0
        for p in range(n - 1):
            if (pairs >> p) & 1:
                # Where exactly two rows have a bit and the carry row is still free, one bit moves into it.
                if not (triples >> p) & 1 and not ((products << 1) >> p) & 1:
                    moves |= 1 << p
                else:
                    products |= 1 << p
        total: list[int | None] = [None] * n
        carry: list[int | None] = [None] * n
        for p in range(n):
            wx, wy, wz = rows[x][p], rows[y][p], rows[z][p]
            if (products >> p) & 1:
                xz, yz = c.xor(wx, wz), c.xor(wy, wz)
                carry[p + 1] = c.xor(c.product(xz, yz), wz)
                total[p] = c.xor(xz, wy)
            elif ((moves & pz) >> p) & 1:
                carry[p], total[p] = wz, c.xor(wx, wy)
            elif ((moves & ~pz) >> p) & 1:
                carry[p], total[p] = wy, wx
            else:
                total[p] = c.xor(c.xor(wx, wz), wy)
        rows[x], rows[y] = total, carry
        present[x], present[y] = px | py | pz, (products << 1) | moves

    c.ripple_carry(rows[live[0]], rows[live[1]])
    return c


def _u64_bilinear(gates: Sequence[Gate], log_size: int) -> Callable[[E, Sequence[E], Sequence[E]], E]:
    def bilinear(alpha: E, row_weights: Sequence[E], column_weights: Sequence[E]) -> E:
        """`e_row^T (A0 + alpha B0) w_col` by one forward walk: every committed wire is a row, whose A side is the
        wire's expansion against `w_col` and whose B side is its other factor, the constant for a free wire or a copy."""
        constant = column_weights[U64_CONSTANT_COLUMN]
        left, right = [ZERO] * 2**log_size, [ZERO] * 2**log_size
        wires: list[E] = []
        for kind, x, y, slot in gates:
            if kind == "xor":
                wires.append(wires[x] + wires[y])
                continue
            slot = x if kind == "free" else slot
            left[slot] = column_weights[slot] if kind == "free" else wires[x]
            right[slot] = wires[y] if kind == "and" else constant
            wires.append(column_weights[slot])
        return dot(row_weights, left) + alpha * dot(row_weights, right)

    return bilinear


FLOCK_CIRCUITS = {
    QFLOCK: FlockCircuit(BLAKE2S_R1CS_LOG_SIZE, BLAKE2S_CONSTANT_COLUMN, blake2s_bilinear),
    QADD: FlockCircuit(8, U64_CONSTANT_COLUMN, _u64_bilinear(_adder().gates, 8)),
    QMUL: FlockCircuit(12, U64_CONSTANT_COLUMN, _u64_bilinear(_multiplier().gates, 12)),
}


def verify_flock(circuit: FlockCircuit, log_height: int, transcript: Transcript) -> tuple[MultilinearPoint, tuple[E, ...]]:
    """The reduction in protocol order: zerocheck, then lincheck. What it leaves is the
    point and the 64 claims s[i] = z(i, point), i < 64, for ring switching to bind."""
    zc = verify_flock_zerocheck(circuit.log_size + log_height, transcript)
    return verify_flock_lincheck(circuit, zc, transcript)


# Ring switching --------------------------------------------------------------

# The Frobenius shifts of the six stages composing Phi, one challenge each.
RING_MAP_SHIFTS = (32, 16, 8, 4, 2, 1)


def _phi(value: E, challenges: Sequence[E]) -> E:
    """The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`."""
    for challenge, shift in zip(challenges, RING_MAP_SHIFTS, strict=True):
        value += challenge * value ** (2**shift)
    return value


def _ring_weight(r: MultilinearPoint, r_prime: Sequence[E], coefficients: Sequence[E]) -> E:
    """The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
    `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`."""
    total = ZERO
    frobenius = list(r)
    for c in coefficients:
        product = c
        for value, challenge in zip(frobenius, r_prime, strict=True):
            product *= ONE + value + challenge
        total += product
        frobenius = [value**2 for value in frobenius]
    return total


def ring_switch(families: Sequence[tuple[MultilinearPoint, Sequence[E]]], transcript: Transcript) -> list[tuple[E, Callable[[Sequence[E]], E]]]:
    """Each family of 64 claims s[i] = z(i, point) becomes one dense claim `sum_u W(u) q(u) = target` on its own packed witness.

    Draw Phi once every family is fixed, the one map serving them all, then take the target
    `T = sum_i x^i Phi(s_i)` against the MLE-friendly weight `W(u) = Phi(eq(point, u))`.
    Returns each family's target and its W as a closure."""
    challenges = transcript.samples(len(RING_MAP_SHIFTS))
    # The same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for k < 64.
    coefficients = [reduce(mul, (f ** (2 ** (k % s)) for f, s in zip(challenges, RING_MAP_SHIFTS) if k & s), ONE) for k in range(K_BITS)]

    def claim(point: MultilinearPoint, s: Sequence[E]) -> tuple[E, Callable[[Sequence[E]], E]]:
        target = poly_eval([_phi(value, challenges) for value in s], GEN)
        return target, lambda r_prime: _ring_weight(point, r_prime, coefficients)

    return [claim(point, s) for point, s in families]


# Stacked opening -------------------------------------------------------------


type StackClaim = tuple[Callable[[Sequence[E]], E], E]  # the weight it puts on the stack, and the value it claims for it


def verify_stacked_opening(transcript: Transcript, root: Digest, stack_log: int, log_inv_rate: int, claims: Sequence[StackClaim]) -> None:
    """Discharge every claim on the committed stack in one opening: the same powers of one challenge
    batch the values into the target, and the weights into the basis WHIR evaluates at its terminal point.
    """
    weights, values = zip(*claims, strict=True)
    scales = powers(transcript.sample(), len(claims))
    verify_whir(transcript, stack_log, log_inv_rate, dot(scales, values), root, lambda point: dot(scales, [weight(point) for weight in weights]))


def verify_execution(bytecode: Sequence[K], public_input: Sequence[K], proof: Proof) -> None:
    require(len(public_input) == 4, "the public input is four words")
    bytecode_hash = blake2s_hash(b"".join(word.to_bytes() for word in bytecode))
    iv_preimage = b"leanvm" + pack("<Q", len(R1CS_DIGEST)) + R1CS_DIGEST + bytecode_hash.value
    fiat_shamir_IV = blake2s_hash(iv_preimage)
    transcript = Transcript(proof, fiat_shamir_IV, public_input)

    # 1] memory log-size, table log-size, log-inv-rate in WHIR, and the clock the run ended on (a K element)
    announced = transcript.next_scalars(3 + len(TABLES))
    require(all(value.c1 == value.c2 == 0 for value in announced), "announced value has a nonzero high limb")
    log_memory = int(announced[0].c0)
    table_logs = tuple(int(value.c0) for value in announced[1 : 1 + len(TABLES)])
    log_inverse_rate = int(announced[-2].c0)
    require(1 <= log_inverse_rate <= 4, "invalid PCS inverse rate")
    layout = build_layout(bytecode, log_memory, table_logs, announced[-1])
    require(MIN_STACKED_LOG <= layout.stack_log <= MAX_STACKED_LOG, "committed size outside the PCS window")

    # 2] parse WHIR commitment: one Merkle root (No OOD, our PCS is only List-binding).
    root = Digest.from_halves(*transcript.next_scalars(2))

    # 3] Bus: one batched GKR over the push, pull and count trees, then the leaf decomposition, which leaves each table a degree-2 claim.
    bus = verify_bus_balance(layout, transcript)

    # 4] One batched (back-loaded) "table sumcheck" over all eight tables, at the bus point, proving the target the three
    # leaf claims derive and that constraints vanish. Every table takes a disjoint range of xi powers for its constraints
    xi = transcript.sample()
    n_constraints = sum(table.n_constraints for table in TABLES)
    xi_powers = powers(xi, n_constraints + 3)  # one power per constraint, then one per bus side, shared by every table
    constraint_powers, form_powers = xi_powers[:n_constraints], xi_powers[n_constraints:]
    target = dot(form_powers, bus.totals)
    table_sumcheck_claims = table_sumcheck(layout.table_log_heights, bus.forms, constraint_powers, form_powers, bus.point, target, transcript)
    claims = [*bus.claims, *table_sumcheck_claims]

    # 5] binding the public words: memory at (r0, r1, 0, ..., 0) is the multilinear extension of the four public words
    # at (r0, r1), both before the run and after it
    public_challenges = transcript.samples(2)
    public_point = (*public_challenges, *[ZERO] * (layout.log_memory - 2))
    public_value = multilinear_eval(public_input, public_challenges)
    claims += [ColumnClaim(column, public_point, public_value) for column in (MEMORY_INITIAL, MEMORY_FINAL)]

    # 6] BLAKE2s, ADD_U64 and MUL_U64 validity via Flock, one reduction per circuit over its own packed witness
    families = [verify_flock(FLOCK_CIRCUITS[witness.column], layout.table_log_heights[witness.table], transcript) for witness in FLOCK_WITNESSES]

    # 7] Ring-switching
    # Each claim is supported on its witness's region of the stack, so its weight carries the
    # placement's selector, and they lead the batch, taking the first powers.
    def on_region(placement: Placement, target: E, weight: Callable[[Sequence[E]], E]) -> StackClaim:
        return (lambda x: placement.eq_above(x) * weight(x[: placement.variables]), target)

    regions = [layout.placements[witness.column] for witness in FLOCK_WITNESSES]
    ringswitches = [on_region(region, *claim) for region, claim in zip(regions, ring_switch(families, transcript), strict=True)]
    verify_stacked_opening(transcript, root, layout.stack_log, log_inverse_rate, [*ringswitches, *(c.on_stack(layout) for c in claims)])
    transcript.finish()


def main(argv: Sequence[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Verify a leanVM execution proof")
    parser.add_argument("bytecode", type=Path, help="stacked bytecode multilinear, little-endian 64-bit words")
    parser.add_argument("public_input", type=Path, help="public input, four little-endian 64-bit words")
    parser.add_argument("stream", type=Path, help="the proof's scalar stream, 24-byte little-endian field elements")
    parser.add_argument("merkle_openings", type=Path, help="every Merkle opening: its leaf's words, then its sibling digests")
    arguments = parser.parse_args(argv)
    try:
        encoded_bytecode = arguments.bytecode.read_bytes()
        require(len(encoded_bytecode) % 8 == 0, "bytecode is not a whole number of 64-bit words")
        bytecode = [K(int.from_bytes(encoded_bytecode[i : i + 8], "little")) for i in range(0, len(encoded_bytecode), 8)]
        encoded_public_input = arguments.public_input.read_bytes()
        require(len(encoded_public_input) == 32, "the public input is four 64-bit words")
        public_input = [K(word) for word in unpack("<4Q", encoded_public_input)]
        proof = Proof.load(arguments.stream, arguments.merkle_openings)
        verify_execution(bytecode, public_input, proof)
    except (OSError, ValueError, KeyError, VerificationError) as exc:
        parser.exit(1, f"verification failed: {exc}\n")
    print("verification succeeded")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
