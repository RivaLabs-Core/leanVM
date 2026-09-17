# Unsigned 64-bit arithmetic: `add_u64` and `mul_u64` read their words as integers
# and wrap, where `+` and `*` are the field's. Eight steps of the linear
# congruential generator x <- x * A + C mod 2^64, a product and a sum each, with
# the second one written straight into its heap cell.
# public_input: 15587117814634046839
from snark_lib import *

A = 6364136223846793005
C = 1442695040888963407
STEPS = 8


def main():
    x = HeapBuf(STEPS + 1)
    x[1] = 81985529216486895
    for i in mul_range(1, GEN ** STEPS):
        x[i * GEN] = add_u64(mul_u64(x[i], A), C)
    p = GEN ** 0
    p[1] = x[GEN ** STEPS]
    return
