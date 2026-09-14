//! `hint_log2_ceil(bits, nbits, floor)`: computed advice returning
//! `g^max(log2_ceil(v), floor)`, where `v` is the integer the `bits` buffer
//! decodes to. The prover fills it at witness-generation (the runtime has `v`
//! concretely); it is unconstrained on its own: `log2_ceil` re-verifies it -
//! so this test checks only that the advice computes the right value.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, g_pow};

use crate::common::pi;

fn log2_ceil_of(v: u64) -> usize {
    if v <= 1 {
        0
    } else {
        (64 - (v - 1).leading_zeros()) as usize
    }
}

fn bits_of(v: u64) -> Vec<F64> {
    (0..8).map(|j| F64((v >> j) & 1)).collect()
}

#[test]
fn log2_ceil_advice_computes_the_log() {
    let src = "\
def main():
    bits = HeapBuf(GEN ** 8)
    hint_witness(bits[0:8], \"bits\")
    g_mu = hint_log2_ceil(bits, 8, 0)
    p = 1
    p[1] = g_mu
    p[GEN] = 1
    return
";
    for v in [1u64, 2, 3, 4, 5, 7, 8, 200] {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("bits", vec![bits_of(v)]);
        let want = pi(&[g_pow(log2_ceil_of(v)), F64::ONE]);
        let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
        verify(&program, &want, &proof).unwrap_or_else(|_| panic!("v={v}: log2_ceil advice must verify"));
        let bad = pi(&[g_pow(log2_ceil_of(v) + 1), F64::ONE]);
        assert!(
            verify(&program, &bad, &proof).is_err(),
            "v={v}: wrong g_mu must be rejected"
        );
    }
}

/// The `floor` argument: `max(log2_ceil(v), floor)`. With floor = 5, small
/// values are lifted to g^5.
#[test]
fn log2_ceil_advice_floor() {
    let src = "\
def main():
    bits = HeapBuf(GEN ** 8)
    hint_witness(bits[0:8], \"bits\")
    g_mu = hint_log2_ceil(bits, 8, 5)
    p = 1
    p[1] = g_mu
    p[GEN] = 1
    return
";
    for (v, mu) in [(2u64, 5usize), (4, 5), (64, 6), (200, 8)] {
        let mut program = compile(&parse(src).expect("parse"));
        program.set_witness("bits", vec![bits_of(v)]);
        let want = pi(&[g_pow(mu), F64::ONE]);
        let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
        verify(&program, &want, &proof).unwrap_or_else(|_| panic!("v={v}: floored log2_ceil must verify"));
    }
}
