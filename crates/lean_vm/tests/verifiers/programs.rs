//! RISC-V programs, proven and checked by both verifiers.

use super::python_verifier::PythonStatement;
use lean_vm::cpu::{Program, prove, verify, verify_to_raw};
use lean_vm::rv::TEXT_BASE;
use lean_vm::rv::asm::*;

const STEPS: u64 = 1000;

/// Fibonacci mod 2^64, iteratively, and the output it proves: `a0 = F(STEPS)`.
pub fn fibonacci() -> (Program, [u64; 4]) {
    let text = Asm::new()
        .li(A0, 0)
        .li(A1, 1)
        .li(T0, STEPS)
        .label("loop")
        .r("add", A2, A0, A1)
        .i("addi", A0, A1, 0)
        .i("addi", A1, A2, 0)
        .i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .li(A1, 0)
        .li(A2, 0)
        .exit()
        .finish();
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..STEPS {
        (a, b) = (b, a.wrapping_add(b));
    }
    (Program::new(&text, TEXT_BASE, vec![], 0), [a, 0, 0, 0])
}

fn proves_and_verifies(tag: &str, program: &Program, expected: [u64; 4]) {
    let (proof, output, _) = prove(program, 1).expect("the run halts");
    assert_eq!(output, expected);
    let raw = verify_to_raw(program, &output, &proof).expect("honest proof verifies");
    PythonStatement::new(tag, program, &output).assert_accepts(&raw);

    let mut wrong = output;
    wrong[0] ^= 1;
    assert!(verify(program, &wrong, &proof).is_err());
}

#[test]
fn fibonacci_proves_and_verifies() {
    let (program, output) = fibonacci();
    proves_and_verifies("fibonacci", &program, output);
}

/// Every instruction of the `ALU` class at least once: the arithmetic and its 32-bit
/// forms, the comparisons, the logic, the constants, all six branches taken and not,
/// and a call and return.
#[test]
fn alu_instructions_prove_and_verify() {
    let mut a = Asm::new();
    // Constants `li` builds without a shift, which is another class's.
    a.li(S0, 0xffff_ffff_8000_0001)
        .li(S1, 0x7fff_ffff)
        .r("add", A0, S0, S1)
        .r("sub", A1, S0, S1)
        .r("addw", A2, S1, S1)
        .r("subw", A3, S0, S1)
        .i("addiw", A4, S1, 1)
        .r("slt", T0, S0, S1)
        .r("sltu", T1, S0, S1)
        .i("slti", T2, S0, -1)
        .i("sltiu", A5, S1, -1)
        .r("and", A6, S0, S1)
        .r("or", A6, A6, T0)
        .r("xor", A6, A6, T1)
        .i("andi", T0, S1, 0x555)
        .i("ori", T0, T0, -0x800)
        .i("xori", T0, T0, 0x2aa)
        .r("add", A0, A0, T0)
        .r("add", A0, A0, T2)
        .r("add", A0, A0, A5)
        .lui(T0, 0xfffff)
        .auipc(T1, 0x12345)
        .r("add", A1, A1, T0)
        .r("add", A1, A1, T1);
    // Each branch twice, operands swapped, so that one of the two is taken. A branch
    // taken skips an increment of a4.
    for (i, op) in ["beq", "bne", "blt", "bge", "bltu", "bgeu"].into_iter().enumerate() {
        for (j, (x, y)) in [(S0, S1), (S1, S0)].into_iter().enumerate() {
            let label: &'static str = Box::leak(format!("skip{i}{j}").into_boxed_str());
            a.branch(op, x, y, label).i("addi", A4, A4, 1).label(label);
        }
    }
    a.jal(RA, "double")
        .jal(RA, "double")
        .li(A3, 0)
        .exit()
        .label("double")
        .r("add", A2, A2, A2)
        .r("add", A4, A4, A4)
        .jalr(ZERO, RA, 0);
    let program = Program::new(&a.finish(), TEXT_BASE, vec![], 0);
    let expected = lean_vm::rv::Machine::new(&program.rv)
        .run(1 << 20)
        .expect("the run halts");
    assert_ne!(expected, [0; 4]);
    proves_and_verifies("alu", &program, expected);
}

/// A run that traps has no proof, and says why.
#[test]
fn a_trap_is_reported() {
    let text = Asm::new().word(0x0010_0073).exit().finish();
    let program = Program::new(&text, TEXT_BASE, vec![], 0);
    assert_eq!(
        prove(&program, 1).err(),
        Some(lean_vm::rv::Trap::Illegal { pc: TEXT_BASE })
    );
}
