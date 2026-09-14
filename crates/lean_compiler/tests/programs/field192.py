# 192-bit arithmetic on three-cell runs: `add192`, `mul192` and `div192` compute in
# GF(2^192) = K[y]/(y^3 + y + 1), limbs low first. A value lives in a StackBuf(3),
# a slice, a list literal or an `f192` constant, crosses a call as a StackBuf(3)
# parameter or return, and reaches the heap through a slice store. The quotient
# is back-solved at witness generation and pinned by the product.
# Published: the limbs of q = (a·b + c) / a, then the low limb of a·b.
# public_input: 5664748180115531082, 13, 4212248646752574772, 1544
from snark_lib import *


def main():
    a = f192(3, 5, 7)
    b = [GEN ** 9, 11, 13]
    c = StackBuf(3)
    c[0] = 17
    c[1] = 19
    c[2] = 23
    heap = HeapBuf(6)
    heap[0:3] = mul192(a, b)
    q = div192(add192(heap[0:3], c), a)
    assert_eq192(mul192(q, a), add192(mul192(a, b), c))
    assert_ne192(q, c)
    assert_eq192(square(q), mul192(q, q))
    heap[3:6] = q
    p = GEN ** 0
    p[0:3] = heap[3:6]
    p[GEN ** 3] = heap[GEN ** 0]
    return


def square(x: StackBuf(3)):
    return mul192(x, x)
