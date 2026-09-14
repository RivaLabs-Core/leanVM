//! `StackBuf`: a run of consecutive frame (stack) cells in the zkDSL. Indexed
//! reads/writes go straight to `base+k` (no heap deref), and a size-4 `StackBuf`
//! is a `blake2s` operand: its four 64-bit cells hold the 256-bit value, so
//! `blake2s(a, b, out)` reads them in place with no copies (a self-hash
//! `blake2s(h, h, out)` aliases one run into both input operands) and writes
//! the digest into the pre-allocated run `out`.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{Op, prove, verify};
use lean_vm::hash_flock::{compression, digest, metadata, unpack_metadata};
use lean_vm::vmhash::compress;
use primitives::field::{F64, g_pow};

use crate::common::{mix, panic_message, pi};

/// A size-4 `StackBuf` fed to `blake2s` as a self-hash `blake2s(h, h)`, then the
/// digest's four words published to `m[0..4]`. Proves and verifies, and a wrong
/// published digest is rejected: so the whole path (StackBuf load → aliased
/// blake2s → heap run store → publish) is exercised end-to-end.
#[test]
fn stack_buf_blake2s_self_hash() {
    let src = "\
def main():
    a = StackBuf(4)
    a[0] = 5
    a[1] = 0
    a[2] = 7
    a[3] = 0
    c = StackBuf(4)
    blake2s(a, a, c)
    p = GEN ** 0
    p[0:4] = c
    return
";
    let program = compile(&parse(src).expect("parse"));
    let h = [5, 0, 7, 0].map(F64);
    let want = compress(h, h);

    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    assert_eq!(mix(src, want)[5], 1, "one BLAKE2s instruction");
    verify(&program, &want, &proof).expect("StackBuf self-hash verifies");

    let mut bad = want;
    bad[0] += F64::ONE;
    assert!(verify(&program, &bad, &proof).is_err(), "wrong digest must be rejected");
}

/// The standard BLAKE2s of the 80 bytes that the words `1, 0, 2, 0, 3, 0, 4, 0, 5, 0`
/// spell little-endian.
fn standard_80_byte_digest() -> [F64; 4] {
    let input: Vec<u8> = [1u64, 0, 2, 0, 3, 0, 4, 0, 5, 0]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    let d = primitives::hash::hash(&input);
    std::array::from_fn(|i| F64(u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap())))
}

/// Optional BLAKE2s metadata and a memory-supplied chaining value reproduce a
/// standard two-block (80-byte) BLAKE2s hash.
#[test]
fn blake2s_keywords_standard_multiblock() {
    let src = "\
def main():
    block0 = [1, 0, 2, 0, 3, 0, 4, 0]
    tail = [5, 0, 0, 0, 0, 0, 0, 0]
    cv = StackBuf(4)
    blake2s(block0[0:4], block0[4:8], cv, counter=64, final=0)
    out = StackBuf(4)
    blake2s(tail[0:4], tail[4:8], out, cv=cv, counter=80, final=1)
    p = GEN ** 0
    p[0:4] = out
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = standard_80_byte_digest();
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    assert_eq!(mix(src, want)[5], 2);
    verify(&program, &want, &proof).expect("standard two-block BLAKE2s verifies");
}

/// The same 80-byte hash with its second block's metadata computed at run time,
/// the shape a hash of runtime length needs: the counter's high part is a word
/// the program produced and its low part a compile-time constant, and their set
/// bits are disjoint, so one `XOR64` is their integer sum (doc
/// §sec:prog-byte-counter). The hint stands in for the high part a real absorb
/// loop derives from its own counter.
#[test]
fn blake2s_runtime_metadata_matches_the_standard_hash() {
    let src = "\
def main():
    block0 = [1, 0, 2, 0, 3, 0, 4, 0]
    tail = [5, 0, 0, 0, 0, 0, 0, 0]
    cv = StackBuf(4)
    blake2s(block0[0:4], block0[4:8], cv, counter=64, final=0)
    high = hint_witness(\"high\")
    assert high == 64
    out = StackBuf(4)
    blake2s(tail[0:4], tail[4:8], out, cv=cv, md=[high + 16, 4294967295])
    p = GEN ** 0
    p[0:4] = out
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("high", vec![vec![F64(64)]]);
    let want = standard_80_byte_digest();
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("a runtime metadata hashes to the standard digest");
}

#[test]
fn blake2s_counter_accepts_full_u64_range() {
    let src = "\
def main():
    block = [1, 0, 2, 0, 3, 0, 4, 0]
    out = StackBuf(4)
    counter = 18446744073709551615 // 1
    blake2s(block[0:4], block[4:8], out, counter=counter, final=1)
    return
";
    let program = compile(&parse(src).expect("parse"));
    // The metadata is a memory operand, so what carries the counter is the `SET`
    // immediates that wrote the two cells the instruction reads.
    let md = program
        .prog
        .iter()
        .find_map(|op| match op {
            Op::Blake2s { md, .. } => Some(*md),
            _ => None,
        })
        .expect("BLAKE2s instruction");
    let set_of = |cell: u32| {
        program
            .prog
            .iter()
            .find_map(|op| match op {
                Op::Set { o, k } if *o == cell => Some(*k),
                _ => None,
            })
            .expect("the metadata cell's SET")
    };
    assert_eq!(unpack_metadata([set_of(md), set_of(md + 1)]), (u64::MAX, u32::MAX, 0));
}

#[test]
#[should_panic(expected = "counter= 18446744073709551616 does not fit in u64")]
fn blake2s_counter_rejects_values_above_u64() {
    let src = "\
def main():
    block = [1, 0, 2, 0, 3, 0, 4, 0]
    out = StackBuf(4)
    blake2s(block[0:4], block[4:8], out, counter=18446744073709551616, final=1)
    return
";
    compile(&parse(src).expect("parse"));
}

/// A default IV first materialized in an untaken runtime branch must not leak
/// into the post-join lowering state. Both executions must initialize the IV
/// on the path that reaches the second hash.
#[test]
fn blake2s_default_iv_after_runtime_branch() {
    let src = "\
def main():
    flag = StackBuf(1)
    hint_witness(flag, \"flag\")
    a = [1, 0, 2, 0, 3, 0, 4, 0]
    if flag[0] == 1:
        ignored = StackBuf(4)
        blake2s(a[0:4], a[4:8], ignored)
    out = StackBuf(4)
    blake2s(a[0:4], a[4:8], out)
    p = GEN ** 0
    p[0:4] = out
    return
";
    let want = compress([1, 0, 2, 0].map(F64), [3, 0, 4, 0].map(F64));
    for flag in [0, 1] {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("flag", vec![vec![F64(flag)]]);
        let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
        verify(&program, &want, &proof).expect("post-join default IV is initialized on both paths");
    }
}

/// Each mutually exclusive branch gets a path-local IV initialization when no
/// dominating default-IV hash exists before the branch.
#[test]
fn blake2s_default_iv_in_both_runtime_branches() {
    let src = "\
def main():
    flag = StackBuf(1)
    hint_witness(flag, \"flag\")
    a = [1, 0, 2, 0, 3, 0, 4, 0]
    out = StackBuf(4)
    if flag[0] == 1:
        blake2s(a[0:4], a[4:8], out)
    else:
        blake2s(a[0:4], a[4:8], out)
    p = GEN ** 0
    p[0:4] = out
    return
";
    let want = compress([1, 0, 2, 0].map(F64), [3, 0, 4, 0].map(F64));
    for flag in [0, 1] {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("flag", vec![vec![F64(flag)]]);
        let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
        verify(&program, &want, &proof).expect("each branch initializes its default IV");
    }
}

/// Deferred aliases may expose non-adjacent source words for a syntactically
/// consecutive CV StackBuf. The compiler must materialize that run because
/// the BLAKE2s opcode carries only one CV base offset.
#[test]
fn blake2s_materializes_aliased_cv_run() {
    let src = "\
def main():
    msg = [1, 0, 2, 0, 3, 0, 4, 0]
    sources = [5, 99, 6, 99, 7, 99, 8]
    cv = [sources[0], sources[2], sources[4], sources[6]]
    out = StackBuf(4)
    blake2s(msg[0:4], msg[4:8], out, cv=cv, counter=128)
    p = GEN ** 0
    p[0:4] = out
    return
";
    let program = compile(&parse(src).expect("parse"));
    let block = compression(
        [1, 0, 2, 0].map(F64),
        [3, 0, 4, 0].map(F64),
        [5, 6, 7, 8].map(F64),
        metadata(128, 0, 0),
    );
    let want = digest(&block);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("materialized custom CV verifies");
}

/// A metadata cell inside the digest destination would be read before the digest
/// is stored and re-read from the finished image by the witness, so the two would
/// disagree and the proof would fail its opening with nothing to point at. Every
/// other overlap is a write-once conflict, which does say where it happened. A
/// partial overlap is enough.
#[test]
#[should_panic(expected = "md= must not name a cell of the digest destination")]
fn blake2s_metadata_inside_the_destination_is_rejected() {
    let src = "\
def main():
    msg = [1, 0, 2, 0, 3, 0, 4, 0]
    out = StackBuf(4)
    out[1] = 7
    blake2s(msg[0:4], msg[4:8], out, md=out[1:3])
    return
";
    compile(&parse(src).expect("parse"));
}

/// Require the caller to state the byte counter explicitly.
#[test]
#[should_panic(expected = "blake2s with cv= requires")]
fn blake2s_cv_alone_is_rejected() {
    let src = "\
def main():
    msg = [1, 0, 2, 0, 3, 0, 4, 0]
    cv = [5, 6, 7, 8]
    out = StackBuf(4)
    blake2s(msg[0:4], msg[4:8], out, cv=cv)
    return
";
    compile(&parse(src).expect("parse"));
}

/// A general (non-blake2s) `StackBuf(3)`: indexed writes, an indexed read feeding
/// an arithmetic write into another slot, then two slots published. Confirms the
/// stack cells are plain consecutive frame cells addressable by index.
#[test]
fn stack_buf_indexing() {
    let src = "\
def main():
    sa = StackBuf(3)
    sa[0] = 3
    sa[1] = 4
    sa[2] = sa[0] + sa[1]
    p = 1
    p[1] = sa[2]
    p[GEN] = sa[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    // `+` is XOR: 3 ^ 4 = 7. Published: (sa[2], sa[1]) = (7, 4).
    let want = pi(&[F64(7), F64(4)]);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    assert_eq!(mix(src, want)[5], 0, "no BLAKE2s here");
    verify(&program, &want, &proof).expect("StackBuf indexing verifies");
}

/// A normal (non-`@inline`) function may return a StackBuf. Its cells cross the
/// call boundary through consecutive return slots and bind as a StackBuf in the
/// caller, including through another normal wrapper function.
#[test]
fn normal_function_returns_stackbuf() {
    let src = "\
def main():
    out = forward(5)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = out[2]
    return

def forward(v):
    out = make(v)
    return out

def make(v):
    out = StackBuf(3)
    out[0] = v
    out[1] = v + 3
    out[2] = 11
    return out
";
    let program = compile(&parse(src).expect("parse"));
    // Field addition is XOR: 5 ^ (5 ^ 3) == 3.
    program.execute(pi(&[F64(3), F64(11)]));
}

/// Tuple returns retain their source-level arity even though a StackBuf member
/// occupies several physical return cells.
#[test]
fn normal_function_returns_stackbuf_and_scalar() {
    let src = "\
def main():
    out, x = make(9)
    p = 1
    p[1] = out[0] + out[1]
    p[GEN] = x
    return

def make(v):
    out = [v, 6]
    return out, v + 1
";
    let program = compile(&parse(src).expect("parse"));
    program.execute(pi(&[F64(15), F64(8)]));
}

/// HeapBuf already crosses a normal call as its one-cell pointer. Allocation
/// happened in the callee, so the caller needs no size metadata to dereference
/// and use the returned buffer.
#[test]
fn normal_function_returns_heapbuf_pointer() {
    let src = "\
def main():
    out = make()
    p = 1
    p[1] = out[1]
    p[GEN] = out[GEN]
    return

def make():
    out = HeapBuf(2)
    out[1] = 17
    out[GEN] = 23
    return out
";
    let program = compile(&parse(src).expect("parse"));
    program.execute(pi(&[F64(17), F64(23)]));
}

/// A StackBuf index literal that does not fit `u32` is rejected at compile time,
/// not silently truncated modulo 2^32 (which would resolve `sa[2^32]` to `sa[0]`).
#[test]
#[should_panic(expected = "does not fit in u32")]
fn stack_buf_index_overflow_rejected() {
    let src = "def main():\n    sa = StackBuf(2)\n    x = sa[4294967296]\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// Rebinding a StackBuf name to a scalar clears the stack binding, so the name
/// is a plain scalar afterward (the old bug left a stale `stacks` entry that made
/// `x` still look like a StackBuf, panicking on scalar use).
#[test]
fn stack_buf_rebind_to_scalar() {
    let src = "def main():\n    x = StackBuf(2)\n    x = 5\n    p = 1\n    p[1] = x\n    p[GEN] = x\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let want = pi(&[F64(5), F64(5)]);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("rebound-scalar program verifies");
}

/// A StackBuf from the enclosing scope referenced inside a `for` loop cannot be
/// captured; the compiler rejects it with a clear message (not a misleading
/// "unbound variable" from the capture being silently dropped).
#[test]
#[should_panic(expected = "cannot be captured into a `for` loop")]
fn stack_buf_loop_capture_rejected() {
    let src = "def main():\n    h = StackBuf(2)\n    h[0] = 1\n    h[1] = 2\n    for i in mul_range(1, GEN ** 4):\n        x = h[0]\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// An `@inline` may return a `StackBuf` *and* a scalar together (a tuple bind):
/// the `StackBuf` slot aliases its cell run into the caller (zero copies, usable
/// as a StackBuf downstream: here fed straight back into a second call, the
/// MD-chain idiom), while the scalar slot binds a value cell. This is the fused
/// `state, x = read_obs(state, cursor)` shape the recursion guest relies on.
#[test]
fn inline_returns_stackbuf_and_scalar() {
    let src = "\
def main():
    s = StackBuf(4)
    s[0] = 5
    s[1] = 0
    s[2] = 7
    s[3] = 0
    s, x = step(s, 9)
    s, y = step(s, x)
    p = GEN ** 0
    p[0:4] = s
    return

@inline
def step(state, v):
    tg = StackBuf(4)
    tg[0] = v
    tg[1] = 0
    tg[2] = 3
    tg[3] = 0
    nb = StackBuf(4)
    blake2s(state, tg, nb)
    return nb, v
";
    let program = compile(&parse(src).expect("parse"));

    // x == v == 9 (the scalar return), so both steps use tag 9.
    let tag = [9, 0, 3, 0].map(F64);
    let s1 = compress([5, 0, 7, 0].map(F64), tag);
    let want = compress(s1, tag); // the returned StackBuf (holding s1's words) fed back in

    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    assert_eq!(mix(src, want)[5], 2, "two BLAKE2s instructions (one per inlined step)");
    verify(&program, &want, &proof).expect("inline StackBuf+scalar tuple return verifies");

    let mut bad = want;
    bad[1] += F64::ONE;
    assert!(
        verify(&program, &bad, &proof).is_err(),
        "wrong published state must be rejected"
    );
}

/// Deferred stores made by a runtime branch must initialize buffers allocated
/// by the surrounding inline call, including when its tuple result is rebound
/// inside an unrolled loop.
#[test]
fn branch_writes_survive_unrolled_tuple_return() {
    let src = "\
def main():
    public = GEN ** 0
    flag = public[1]
    a = [5, 7]
    b = [13, 17]
    for i in unroll(0, 1):
        a, b = select_pair(flag, a, b)
    assert a[0] == 13
    assert a[1] == 17
    assert b[0] == 5
    assert b[1] == 7
    return

@inline
def select_pair(flag, a, b):
    first = StackBuf(2)
    second = StackBuf(2)
    if flag == 0:
        first[0] = a[0]
        first[1] = a[1]
        second[0] = b[0]
        second[1] = b[1]
    else:
        first[0] = b[0]
        first[1] = b[1]
        second[0] = a[0]
        second[1] = a[1]
    return first, second
";
    let program = compile(&parse(src).expect("parse"));
    program.execute(pi(&[F64::ONE]));
}

/// An `@inline` may also alias-return a folded **g-address** among its values:
/// `fs, x, cur = step(fs, cur)` hands back the Fiat-Shamir state (StackBuf), the
/// consumed word (scalar), and the ADVANCED cursor (`cursor * GEN`) as a
/// zero-cost folded pointer, so the caller keeps reading through it with no
/// manual `cur *= GEN`. This is the shape `fs_next` uses to walk the stream.
#[test]
fn inline_returns_advanced_cursor() {
    let src = "\
def main():
    hb = HeapBuf(4)
    hb[1] = 10
    hb[GEN] = 20
    hb[GEN ** 2] = 30
    fs = StackBuf(4)
    fs[0] = 1
    fs[1] = 0
    fs[2] = 2
    fs[3] = 0
    cur = hb
    fs, a, cur = step(fs, cur)
    fs, b, cur = step(fs, cur)
    v = cur[GEN ** 0]
    p = 1
    p[1] = a + b
    p[GEN] = v
    return

@inline
def step(state, cursor):
    x = cursor[GEN ** 0]
    tg = StackBuf(4)
    tg[0] = x
    tg[1] = 0
    tg[2] = 3
    tg[3] = 0
    nb = StackBuf(4)
    blake2s(state, tg, nb)
    return nb, x, cursor * GEN
";
    let program = compile(&parse(src).expect("parse"));
    // a = hb[0] = 10, b = hb[1] = 20, v = hb[2] = 30 read through the cursor
    // returned twice-advanced. a + b is XOR: 10 ^ 20 = 30.
    let want = pi(&[F64(30), F64(30)]);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("inline advanced-cursor return verifies");
}

/// `x = [a, b, c, d]`: the list-literal StackBuf initializer: allocates the run
/// and writes the elements in place, sugar for alloc-then-store. The test mixes a
/// runtime value, a constant, and an expression; feeds the result to blake2s; and
/// swaps a buffer through itself (`s = [s[1], s[0], …]` reads the OLD binding,
/// per the let-rebind rule).
#[test]
fn stack_buf_list_literal() {
    let src = "\
def main():
    s = [5, 7, 0, 0]
    s = [s[1], s[0], s[2], s[3]]
    t = [s[0] + s[1], 3, 0, 0]
    out = StackBuf(4)
    blake2s(s, t, out)
    p = GEN ** 0
    p[0:4] = out
    return
";
    let program = compile(&parse(src).expect("parse"));
    // s = [7, 5, 0, 0] after the swap; t = [7 ^ 5, 3, 0, 0] = [2, 3, 0, 0].
    let want = compress([7, 5, 0, 0].map(F64), [2, 3, 0, 0].map(F64));
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    assert_eq!(mix(src, want)[5], 1, "one BLAKE2s instruction");
    verify(&program, &want, &proof).expect("list-literal StackBuf verifies");
}

/// A list literal anywhere but the RHS of an assignment is rejected with a
/// clear message, not lowered as a phantom scalar.
#[test]
#[should_panic(expected = "a list literal must be bound to a name")]
fn stack_buf_list_literal_as_value_rejected() {
    let src = "def main():\n    x = 1 + [2, 3]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A compile-time heap index past the buffer's declared size is a compile
/// error, not a runtime wild deref.
#[test]
#[should_panic(expected = "heap index 8 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    x = hb[GEN ** 8]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// The bound follows shifted aliases back to the original buffer: a pointer
/// alias `row = hb * GEN ** k` checks `row[GEN ** j]` against size − k.
#[test]
#[should_panic(expected = "heap index 9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_alias_index_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    row = hb * GEN ** 6\n    x = row[GEN ** 3]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A hint slice whose end exceeds the buffer is rejected at compile time.
#[test]
#[should_panic(expected = "heap slice 0:9 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_hint_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hint_witness(hb[0:9], \"w\")\n    x = hb[GEN ** 0]\n    assert x == x\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A blake2s heap slice straddling the buffer end is rejected. The 256-bit
/// operand `hb[6:10]` is four 64-bit cells, so the bound check trips at
/// `6 + 4 = 10 > 8`.
#[test]
#[should_panic(expected = "heap slice 6:10 out of bounds for `hb` (HeapBuf size 8)")]
fn heap_blake2s_slice_oob_rejected() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    out = StackBuf(4)\n    blake2s(hb[6:10], hb[6:10], out)\n    return\n";
    let _ = compile(&parse(src).expect("parse"));
}

/// A heap index that folds to a non-g-power field constant (an integer loop
/// var leaking in from a StackBuf conversion) can never name a heap cell (cell
/// k lives at `buf · g^k`) and used to survive to proving time as a
/// wild-pointer DEREF. It must be a compile-time error.
#[test]
#[should_panic(expected = "not a g-power")]
fn integer_heap_index_is_rejected() {
    let src = "\
def main():
    b = HeapBuf(4)
    b[1] = 3
    b[GEN] = 5
    x = 0
    for k in unroll(0, 2):
        p = 1
        p[GEN ** k] = b[k]
    return
";
    compile(&parse(src).expect("parse"));
}

/// The last in-bounds index still compiles and runs.
#[test]
fn heap_index_boundary_ok() {
    let src = "def main():\n    hb = HeapBuf(8)\n    hb[GEN ** 7] = 5\n    row = hb * GEN ** 4\n    y = row[GEN ** 3]\n    assert y == 5\n    return\n";
    let program = compile(&parse(src).expect("parse"));
    let pi = pi(&[F64(3), F64(4)]);
    let (proof, _) = prove(&program, pi, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &pi, &proof).expect("boundary access verifies");
}

/// A store into a run PARAMETER is the write-once assertion, not a fresh store.
///
/// A run parameter's cells are already written, by the caller, before the
/// callee's first instruction; a local `StackBuf`'s are not. That is the whole
/// difference, and missing it dropped the assertion: `s[k] = <value>` inside a
/// callee recorded a deferred alias and emitted nothing, so the idiom that pins
/// an unconstrained hint pinned nothing and the prover kept its own values.
#[test]
fn a_store_into_a_run_parameter_asserts() {
    let pin = "\
def pin(s: StackBuf(2)):
    s[0] = GEN ** 5
    s[1] = GEN ** 6
    return GEN ** 0

def main():
    b = StackBuf(2)
    hint_witness(b, \"adv\")
    z = pin(b)
    p = GEN ** 0
    p[1] = b[0]
    p[GEN] = b[1]
    return
";
    let ast = parse(pin).expect("parse");
    // The honest prover hints what the callee asserts, and it verifies.
    let mut program = compile(&ast);
    program.set_witness("adv", vec![vec![g_pow(5), g_pow(6)]]);
    let want = pi(&[g_pow(5), g_pow(6)]);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the honest hint matches the pin");

    // A prover hinting anything else must be rejected: that is what the pin is.
    let mut bad = compile(&ast);
    bad.set_witness("adv", vec![vec![g_pow(13), g_pow(14)]]);
    let dishonest = pi(&[g_pow(13), g_pow(14)]);
    assert!(
        std::panic::catch_unwind(|| bad.execute(dishonest)).is_err(),
        "the pin must reject a hint it does not match"
    );

    // The same rule with no hint involved: one cell cannot hold two values.
    let two = "\
def f(s: StackBuf(2)):
    s[0] = s[1]
    return s[0]

def main():
    b = StackBuf(2)
    b[0] = GEN ** 9
    b[1] = GEN ** 3
    r = f(b)
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
";
    let program = compile(&parse(two).expect("parse"));
    let want = pi(&[g_pow(3), g_pow(0)]);
    assert!(
        std::panic::catch_unwind(|| program.execute(want)).is_err(),
        "`s[0] = s[1]` asserts that they are equal"
    );
}

/// A multi-cell value can cross a call in BOTH directions.
///
/// It could always be returned as a run of cells and never passed as one, so a
/// multi-cell digest went in through a pointer or an `@inline` expansion while
/// coming back out whole. A `s: StackBuf(n)` parameter takes the same n
/// consecutive cells a `StackBuf(n)` return value occupies, placed by the same
/// `Abi`, which is why the argument area is now a WIDTH rather than a count.
#[test]
fn a_stack_buf_can_be_passed_as_well_as_returned() {
    let src = "\
def swap(s: StackBuf(2)):
    t = StackBuf(2)
    t[0] = s[1]
    t[1] = s[0]
    return t

def main():
    b = StackBuf(2)
    b[0] = GEN ** 1
    b[1] = GEN ** 2
    r = swap(b)
    p = GEN ** 0
    p[1] = r[0]
    p[GEN] = r[1]
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = pi(&[g_pow(2), g_pow(1)]);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the run went in and the swapped run came back");

    // The shape is checked at the call, in both directions of mismatch.
    for (arg, want) in [
        (
            "b = StackBuf(3)\n    b[0] = GEN ** 1\n    r = f(b)",
            "got a 3-cell value",
        ),
        ("r = f(GEN ** 1)", "pass a 2-cell value"),
    ] {
        let src = format!(
            "def f(s: StackBuf(2)):\n    return s[0]\n\ndef main():\n    {arg}\n    p = GEN ** 0\n    p[1] = r\n    p[GEN] = GEN ** 0\n    return\n"
        );
        let ast = parse(&src).expect("parses");
        let Err(err) = std::panic::catch_unwind(|| compile(&ast)) else {
            panic!("accepted: {arg}");
        };
        let msg = panic_message(&*err);
        assert!(msg.contains(want), "got `{msg}`");
    }
}

/// `g` is `x`, so the literal `2^k` IS `g^k`. `try_gpow_index` always knew that
/// and `gaddr_of` did not, so one field element had three answers: `hb[GEN * 2]`
/// was rejected as "not a g-power" while `hb[GEN * GEN]` compiled, and
/// `hb[r * 2]` compiled again as soon as `r` was runtime. All three name cell 2.
/// A BARE literal index stays rejected: see `integer_heap_index_is_rejected`.
#[test]
fn a_literal_power_of_two_is_a_g_power() {
    let src = "\
def main():
    hb = HeapBuf(8)
    hb[GEN * GEN] = GEN ** 5
    p = GEN ** 0
    p[1] = hb[GEN * 2]
    p[GEN] = hb[GEN ** 2]
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = pi(&[g_pow(5), g_pow(5)]);
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("three spellings of cell 2 agree");
}
