# `Const` parameters: `def hash_pair(buf, k: Const)` is a template: each call
# site passes a compile-time constant and gets a monomorphized copy with `k`
# substituted as the integer literal, usable in compile-time positions (the
# slice bounds below). The direct call and match arm 0 share the k=0
# specialization. A 256-bit BLAKE2s value occupies four cells.
# Published: the four digest words of H(quad0, quad0) XOR H(quad1, quad1): the
# direct k=0 digest XORed with the arm the runtime x = GEN selects (k=1).
# public_input: 10463089001937318211, 13689025457361823030, 10489568288789412215, 14305888178150900108
from snark_lib import *


def main():
    buf = HeapBuf(8)
    buf[0:8] = [5, 0, 7, 0, 11, 0, 13, 0]
    a0, a1, a2, a3 = hash_pair(buf, 0)
    x = GEN
    b0, b1, b2, b3 = match(log(x), range(0, 2), lambda i: hash_pair(buf, i))
    p = GEN ** 0
    p[1] = a0 + b0
    p[GEN] = a1 + b1
    p[GEN ** 2] = a2 + b2
    p[GEN ** 3] = a3 + b3
    return


def hash_pair(buf, k: Const):
    h = StackBuf(4)
    blake2s(buf[k * 4:k * 4 + 4], buf[k * 4:k * 4 + 4], h)
    return h[0], h[1], h[2], h[3]
