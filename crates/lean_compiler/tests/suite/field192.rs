//! 192-bit values: runs of three cells, limbs low first, computed by `add192`,
//! `mul192` and `div192`. A run and a scalar never stand in for each other, runs
//! cross the heap in both directions, and the quotient back-solve refuses a zero
//! divisor. The soundness of the arithmetic itself is in `soundness`.

use lean_compiler::{compile, compile_without_filler, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

use crate::common::panic_message;

/// Where a 192-bit value and a scalar meet, the program is rejected with a
/// diagnostic naming the widths, rather than one side reading the other's first
/// cell or a statement dropping a value on the floor.
#[test]
fn a_run_and_a_scalar_do_not_stand_in_for_each_other() {
    for (body, want) in [
        (
            "y = add192(f192(1, 2, 3), f192(4, 5, 6)) + 1",
            "is a 192-bit value, a run of three cells, not a scalar",
        ),
        ("x = f192(1, 2, 3)\n    assert x == 5", "used as a scalar"),
        (
            "y = mul192(GEN, f192(4, 5, 6))",
            "expected a 3-cell value, got the scalar",
        ),
        (
            "h = StackBuf(4)\n    y = mul192(h, f192(4, 5, 6))",
            "expected a 3-cell value, got a 4-cell one",
        ),
        (
            "assert_eq192(f192(1, 2, 3), GEN)",
            "expected a 3-cell value, got the scalar",
        ),
        (
            "add192(f192(1, 2, 3), f192(4, 5, 6))",
            "is a 192-bit value, not a statement",
        ),
        (
            "hb = HeapBuf(4)\n    hb[0:4] = f192(1, 2, 3)",
            "expected a 4-cell value, got a 3-cell one",
        ),
        (
            "s = StackBuf(2)\n    s[0:2] = mul192(f192(1, 2, 3), f192(4, 5, 6))",
            "expected a 2-cell value, got a 3-cell one",
        ),
        ("r = sq(GEN)", "pass a 3-cell value"),
        ("y = f192(1, 2)", "takes three limbs"),
        (
            "y = f192(1, 2, 18446744073709551616)",
            "an f192 limb is a compile-time 64-bit integer",
        ),
    ] {
        let src = format!("def sq(x: StackBuf(3)):\n    return mul192(x, x)\n\ndef main():\n    {body}\n    return\n");
        let msg = match parse(&src) {
            Err(e) => e,
            Ok(ast) => match std::panic::catch_unwind(|| compile(&ast)) {
                Err(err) => panic_message(&*err),
                Ok(_) => panic!("accepted: {body}"),
            },
        };
        assert!(msg.contains(want), "`{body}`: wanted `{want}`, got `{msg}`");
    }
}

/// A run read off the heap and stored back is the same value: runtime heap slices
/// written and read in a loop (a cached pair of loads per iteration), a stack copy
/// of a heap run, a list flattening two runs into one buffer, and a heap run
/// store publishing the result. The published scalar is the heap cell holding
/// the low limb, which pins the limb order.
#[test]
fn heap_runs_round_trip() {
    let src = "\
def main():
    x = StackBuf(3)
    hint_witness(x, \"x\")
    heap = HeapBuf(12)
    heap[0:3] = x
    for i in mul_range(1, GEN ** 3):
        b = i ** 3
        heap[b * GEN ** 3:b * GEN ** 3 + 3] = mul192(heap[b:b + 3], heap[b:b + 3])
    y = heap[9:12]
    both = [y, heap[0:3]]
    assert_eq192(both[3:6], x)
    p = GEN ** 0
    p[0:3] = both[0:3]
    p[GEN ** 3] = heap[GEN ** 9]
    return
";
    let x = F192::new(g_pow(7).0, 0x0123_4567_89ab_cdef, 42);
    let y = (0..3).fold(x, |acc, _| acc * acc);
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("x", vec![vec![F64(x.c0), F64(x.c1), F64(x.c2)]]);
    let want = [F64(y.c0), F64(y.c1), F64(y.c2), F64(y.c0)];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("x^8 comes back off the heap");

    let mut bad = want;
    bad[2] += F64::ONE;
    assert!(verify(&program, &bad, &proof).is_err(), "the top limb is bound");
}

/// `div192` by zero has no quotient, so the back-solve refuses it rather than
/// writing one the product cannot check. A divisor with zero low limbs is not
/// zero, so it divides.
#[test]
fn div192_by_zero_is_rejected() {
    let src = "\
def main():
    d = StackBuf(3)
    hint_witness(d, \"d\")
    q = div192(f192(1, 0, 0), d)
    p = GEN ** 0
    p[0:3] = mul192(q, d)
    return
";
    let program = compile_without_filler(&parse(src).expect("parse"));
    let run = |d: [u64; 3]| {
        let mut p = program.clone();
        p.set_witness("d", vec![d.map(F64).to_vec()]);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            p.execute([F64::ONE, F64::ZERO, F64::ZERO, F64::ZERO])
        }))
    };
    assert!(run([0, 0, 1]).is_ok(), "y^2 is invertible");
    let Err(err) = run([0, 0, 0]) else {
        panic!("a zero divisor has no quotient");
    };
    let msg = panic_message(&*err);
    assert!(msg.contains("zero operand"), "got `{msg}`");
}

/// A `div192` stored into a run already holding some of the quotient's limbs
/// asserts those and fills the rest, as any store into written cells does: the
/// relation `q · b == a` determines every limb once `b` is nonzero.
#[test]
fn div192_into_a_partly_written_run() {
    let src = "\
def main():
    q = StackBuf(3)
    q[0] = FIRST
    q[0:3] = div192(mul192(f192(3, 5, 7), f192(11, 13, 17)), f192(11, 13, 17))
    p = GEN ** 0
    p[0:3] = q
    return
";
    let program = compile(&parse(&src.replace("FIRST", "3")).expect("parse"));
    let want = [F64(3), F64(5), F64(7), F64::ZERO];
    let (proof, _) = prove(&program, want, lean_vm::pcs::TEST_LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the written limb agrees with the quotient");

    let wrong = compile_without_filler(&parse(&src.replace("FIRST", "4")).expect("parse"));
    assert!(
        std::panic::catch_unwind(|| wrong.execute(want)).is_err(),
        "a written limb that disagrees with the quotient is rejected"
    );
}
