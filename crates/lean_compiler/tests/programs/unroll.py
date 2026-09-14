# `for i in unroll(a, b)` replicates the body at compile time, i substituted
# as the integer literal of each iteration: zero loop overhead (no call, no
# frame, no counter). Bounds are compile-time integers, including Const
# parameters: `chain(buf, 3)` specializes and unrolls three BLAKE2s steps over
# heap slices indexed by `i` (a 256-bit BLAKE2s value is four cells).
# Published: the four digest words of H^3(5, 7): same chain as
# hash_heap_chain.py, unrolled instead of looped.
# public_input: 248045690890498167, 3488266399269529831, 15161625676544491720, 8881774354923095707
from snark_lib import *


def main():
    sb = StackBuf(8)
    sb[0] = 1
    for i in unroll(0, 7):
        sb[i + 1] = sb[i] * GEN  # sb[k] = g^k
    assert sb[7] == GEN ** 7
    buf = HeapBuf(16)
    buf[0:4] = [5, 0, 7, 0]
    chain(buf, 3)
    p = GEN ** 0
    p[0:4] = buf[12:16]
    return


def chain(buf, n: Const):
    for i in unroll(0, n):
        blake2s(buf[i * 4:i * 4 + 4], buf[i * 4:i * 4 + 4], buf[i * 4 + 4:i * 4 + 8])
    return
