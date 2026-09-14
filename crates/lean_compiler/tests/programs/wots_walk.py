# A miniature WOTS-style chain walk bundling the DSL's moving parts: a
# runtime digit is range-checked (dispatch soundness), then match
# dispatches it to a Const-specialized walker whose BLAKE2s chain is unrolled
# over heap slices (a 256-bit BLAKE2s value occupies four cells); the walker
# reads its final digest back through a folded g^{4n} pointer. The
# recomputation at the end lands on an already-written run, so write-once
# turns the hash into a digest assertion; the dead `if` branch holds an
# impossible assert that must never execute. Published: the four digest words
# of H^2(5, 7).
# public_input: 14532901099560457711, 11823874305988834691, 15091288840866790244, 16695971830359737202
from snark_lib import *


def main():
    buf = HeapBuf(16)
    buf[0:4] = [5, 0, 7, 0]
    d = GEN ** 2  # the runtime digit
    assert log(d) < 4  # bound the scrutinee before dispatching on it
    t0, t1, t2, t3 = match(log(d), range(0, 4), lambda i: walk(buf, i))
    if d != GEN ** 2:
        assert 1 == 0  # dead branch: never executes
    v = [t0, t1, t2, t3]
    blake2s(buf[4:8], buf[4:8], v)  # recompute H(value1, value1): asserts v == (t0, t1, t2, t3)
    p = GEN ** 0
    p[0:4] = v
    return


def walk(buf, n: Const):
    p = 1
    for i in unroll(0, n):
        blake2s(buf[i * 4:i * 4 + 4], buf[i * 4:i * 4 + 4], buf[i * 4 + 4:i * 4 + 8])
        p = p * GEN ** 4
    return buf[p], buf[p * GEN], buf[p * GEN ** 2], buf[p * GEN ** 3]
