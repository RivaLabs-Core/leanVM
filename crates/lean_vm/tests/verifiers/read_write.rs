//! Programs that only read-write memory can run: every cell of their loop is
//! overwritten each iteration, one of them by an instruction that also reads it,
//! and a digest lands on the cells it was computed from. Proven, and checked by both
//! verifiers.

use super::python_verifier::PythonStatement;
use lean_vm::cpu::{DerefMode, Op, Program, prove, verify, verify_to_raw};
use lean_vm::hash_flock::{compression, digest};
use primitives::field::{F64, g_pow};

const STEPS: usize = 1000;

// The frame, past the four public words.
const A: u32 = 4;
const B: u32 = 5;
const T: u32 = 6;
const I: u32 = 7;
const GEN: u32 = 8;
const END: u32 = 9;
const COND: u32 = 10;
const LOOP_PC: u32 = 11;
const FRAME: u32 = 12;
const ONE: u32 = 13;
const PTR: u32 = 14;
/// A four-word hash state, then two zero metadata words.
const STATE: u32 = 16;
const MD: u32 = 20;
/// Where the heap store lands, through `PTR`.
const HEAP: u32 = 24;
const FRAME_CELLS: u32 = 32;

/// Fibonacci in the exponent, in place: `(a, b) ← (b, a·b)` for `STEPS` rounds of one
/// loop over the same seven cells, then `g^{F(STEPS)}` stored through a pointer and
/// published into `m[0]`, and a hash state compressed onto itself twice.
fn program() -> Program {
    let set = |o: u32, k: F64| Op::Set { o, k };
    let mut body = vec![
        set(A, F64::ONE),
        set(B, g_pow(1)),
        set(I, F64::ONE),
        set(GEN, g_pow(1)),
        set(END, g_pow(STEPS)),
        set(FRAME, F64::ONE),
        set(ONE, F64::ONE),
        set(PTR, g_pow(HEAP as usize)),
    ];
    let top = body.len() + 1;
    body.push(set(LOOP_PC, g_pow(top)));
    body.extend([
        Op::Mul64 { a: A, b: B, c: T },
        Op::Mul64 { a: B, b: ONE, c: A },
        Op::Mul64 { a: T, b: ONE, c: B },
        // The counter advances where it sits: one row reads and writes the cell.
        Op::Mul64 { a: I, b: GEN, c: I },
        Op::Xor64 { a: I, b: END, c: COND },
        Op::Jump {
            oc: COND,
            od: LOOP_PC,
            of: FRAME,
        },
        Op::Deref {
            o1: PTR,
            o2: 0,
            o3: A,
            mode: DerefMode::Cell,
        },
        Op::Mul64 { a: A, b: ONE, c: 0 },
    ]);
    let hash = Op::Blake2s {
        ins: [STATE, STATE + 2, STATE, STATE + 2],
        cv: STATE,
        out: STATE,
        md: MD,
    };
    body.extend([hash, hash]);
    Program::from_body(body, FRAME_CELLS)
}

/// [`program`] with the public input it proves: `g^{F(STEPS)}`, then zeros.
pub fn fibonacci() -> (Program, [F64; 4]) {
    let (mut a, mut b) = (F64::ONE, g_pow(1));
    for _ in 0..STEPS {
        (a, b) = (b, a * b);
    }
    (program(), [a, F64::ZERO, F64::ZERO, F64::ZERO])
}

#[test]
fn read_write_program_proves_and_verifies() {
    let (program, public_input) = fibonacci();
    let a = public_input[0];

    let exec = program.execute(public_input);
    assert_eq!(exec.mem[HEAP as usize], a, "the heap store");
    let mut state = [F64::ZERO; 4];
    for _ in 0..2 {
        state = digest(&compression(state, state, state, [F64::ZERO; 2]));
    }
    assert_eq!(exec.mem[STATE as usize..STATE as usize + 4], state, "the in-place hash");
    assert_ne!(exec.init, exec.mem, "the run rewrote its memory");

    let (proof, _) = prove(&program, public_input, 1);
    let raw = verify_to_raw(&program, &public_input, &proof).expect("honest proof verifies");
    PythonStatement::new("read-write", &program, &public_input).assert_accepts(&raw);

    let mut wrong = public_input;
    wrong[0] += F64::ONE;
    assert!(verify(&program, &wrong, &proof).is_err());
}

/// A 64-bit linear congruential generator, `x ← x·A + C mod 2^64`, stepped in place:
/// `MUL_U64` and `ADD_U64` each overwrite the operand they read.
fn lcg_program(seed: u64) -> Program {
    const X: u32 = 4;
    const MULTIPLIER: u32 = 5;
    const INCREMENT: u32 = 6;
    let set = |o: u32, k: F64| Op::Set { o, k };
    let mut body = vec![
        set(X, F64(seed)),
        set(MULTIPLIER, F64(LCG_A)),
        set(INCREMENT, F64(LCG_C)),
        set(I, F64::ONE),
        set(GEN, g_pow(1)),
        set(END, g_pow(STEPS)),
        set(FRAME, F64::ONE),
        set(ONE, F64::ONE),
    ];
    let top = body.len() + 1;
    body.push(set(LOOP_PC, g_pow(top)));
    body.extend([
        Op::MulU64 {
            a: X,
            b: MULTIPLIER,
            c: X,
        },
        Op::AddU64 {
            a: X,
            b: INCREMENT,
            c: X,
        },
        Op::Mul64 { a: I, b: GEN, c: I },
        Op::Xor64 { a: I, b: END, c: COND },
        Op::Jump {
            oc: COND,
            od: LOOP_PC,
            of: FRAME,
        },
        Op::Mul64 { a: X, b: ONE, c: 0 },
    ]);
    Program::from_body(body, FRAME_CELLS)
}

const LCG_A: u64 = 6_364_136_223_846_793_005;
const LCG_C: u64 = 1_442_695_040_888_963_407;

#[test]
fn u64_arithmetic_proves_and_verifies() {
    let seed = 0x0123_4567_89ab_cdef;
    let program = lcg_program(seed);
    let x = (0..STEPS).fold(seed, |x, _| x.wrapping_mul(LCG_A).wrapping_add(LCG_C));
    let public_input = [F64(x), F64::ZERO, F64::ZERO, F64::ZERO];

    let (proof, stats) = prove(&program, public_input, 1);
    assert_eq!(
        stats.base_counts[6..],
        [STEPS, STEPS],
        "one ADD_U64 and one MUL_U64 a step"
    );
    let raw = verify_to_raw(&program, &public_input, &proof).expect("honest proof verifies");
    PythonStatement::new("u64", &program, &public_input).assert_accepts(&raw);

    let mut wrong = public_input;
    wrong[0] += F64::ONE;
    assert!(verify(&program, &wrong, &proof).is_err());
}
