//! Rust guests (`guests/`), from their ELF files: compiled by `rustc` for
//! `riscv64im-unknown-none-elf`, loaded, run, proven, and checked by both verifiers.
//! The files are built by `guests/build.sh` and checked in, the target needing a
//! nightly toolchain.

use super::python_verifier::PythonStatement;
use lean_vm::cpu::{Program, prove, verify, verify_to_raw};
use lean_vm::rv::{Guest, Machine};

fn proves_and_verifies(tag: &str, elf: &[u8], input: [u64; 4], expected: [u64; 4]) {
    let program = Program::from_elf(elf).expect("a guest");
    let ran = Machine::new(&program.rv, input).run(1 << 24).expect("the run halts");
    assert_eq!(ran, expected, "{tag}: the interpreter");

    let (proof, output, stats) = prove(&program, input, 1).expect("the run halts");
    assert_eq!(output, expected);
    let raw = verify_to_raw(&program, &input, &output, &proof).expect("honest proof verifies");
    PythonStatement::new(tag, &program, &input, &output).assert_accepts(&raw);
    let mut wrong = output;
    wrong[3] ^= 1;
    assert!(verify(&program, &input, &wrong, &proof).is_err());
    println!("{tag}: {} instructions, {}", program.rv.entries.len(), stats.details());
}

#[test]
fn fibonacci_guest() {
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..5000 {
        (a, b) = (b, a.wrapping_add(b));
    }
    proves_and_verifies(
        "fibonacci",
        include_bytes!("../../../../guests/elf/fibonacci.elf"),
        [5000, 0, 0, 0],
        [a, 0, 0, 0],
    );
}

/// BLAKE2s-256 in plain Rust on the VM, against the prover's own BLAKE2s: shifts,
/// rotations, 32-bit arithmetic, byte loads and stores, a message that is not a whole
/// number of blocks.
#[test]
fn blake2s_guest() {
    let length = 150u64;
    let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
    let digest = primitives::hash::Hasher::new().update(&message).finalize();
    let expected = std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()));
    proves_and_verifies(
        "blake2s",
        include_bytes!("../../../../guests/elf/blake2s.elf"),
        [length, 0, 0, 0],
        expected,
    );
}

/// The same digest through the `blake2s` instruction, from the runtime's hasher: the
/// precompile as a guest reaches it, on a message of several blocks.
#[test]
fn hash_guest() {
    let length = 1000u64;
    let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
    let digest = primitives::hash::Hasher::new().update(&message).finalize();
    let expected = std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()));
    proves_and_verifies(
        "hash",
        include_bytes!("../../../../guests/elf/hash.elf"),
        [length, 0, 0, 0],
        expected,
    );
}

/// Multiplications and divisions as `rustc` emits them, 128-bit arithmetic included.
#[test]
fn numbers_guest() {
    let (base, exponent, modulus) = (0x1234_5678_9abc_def1u64, 65_537u64, 0xffff_ffff_0000_0001u64);
    let pow_mod = {
        let (mut result, mut b, mut e) = (1u128, base as u128 % modulus as u128, exponent);
        while e > 0 {
            if e & 1 == 1 {
                result = result * b % modulus as u128;
            }
            b = b * b % modulus as u128;
            e >>= 1;
        }
        result as u64
    };
    let gcd = {
        let (mut a, mut b) = (base, modulus);
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let signed = (base as i64).wrapping_neg() / (exponent as i64 | 1);
    let mixed = ((base as i32) / (exponent as i32 | 1)) as i64 % 1000;
    proves_and_verifies(
        "numbers",
        include_bytes!("../../../../guests/elf/numbers.elf"),
        [base, exponent, modulus, 0],
        [pow_mod, gcd, signed as u64, mixed as u64],
    );
}

/// What is not a guest is refused by name, not run.
#[test]
fn malformed_elf_files_are_refused() {
    let elf = include_bytes!("../../../../guests/elf/fibonacci.elf");
    assert!(Guest::from_elf(elf).is_ok());
    assert!(Guest::from_elf(&elf[..40]).is_err(), "a truncated header");
    for (at, value, what) in [
        (4usize, 1u8, "32-bit"),
        (16, 3, "a PIE"),
        (18, 62, "x86-64"),
        (48, 1, "compressed"),
    ] {
        let mut bad = elf.to_vec();
        bad[at] = value;
        assert!(Guest::from_elf(&bad).is_err(), "{what}");
    }
}
