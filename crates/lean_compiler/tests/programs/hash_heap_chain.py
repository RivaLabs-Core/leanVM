# Runtime slices: `buf[i:i + 4]` with a runtime g-power index `i` names the
# heap cells `buf·i·g^k`, k < 4 (one MUL folds `i` into the pointer). A BLAKE2s
# chain over heap runs (a 256-bit BLAKE2s value is four cells), addressed by the
# loop counter: value k sits at cells g^{4k}..g^{4k+3}, and value k+1 =
# H(value k, value k). Published: the four digest words of H^3(5, 7).
# public_input: 248045690890498167, 3488266399269529831, 15161625676544491720, 8881774354923095707
from snark_lib import *


def main():
    buf = HeapBuf(16)
    buf[0:4] = [5, 0, 7, 0]
    for i in mul_range(1, GEN ** 3):
        b = i ** 4  # value k at cells g^{4k}..g^{4k+3}
        blake2s(buf[b:b + 4], buf[b:b + 4], buf[b * GEN ** 4:b * GEN ** 4 + 4])
    p = GEN ** 0
    p[0:4] = buf[12:16]
    return
