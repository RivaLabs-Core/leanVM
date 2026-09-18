use leanvm::asm::*;
use leanvm::*;

/// `a0 <- F(n) mod 2^64`, `n` being the first word of the public input, by a loop that
/// keeps its two numbers on the stack.
fn fibonacci() -> Program {
    const LOG_RAM: usize = 4;
    let text = Asm::new()
        .li(SP, RAM_BASE + (8 << LOG_RAM) - 16)
        .li(T0, RAM_BASE)
        .load("ld", T0, 0, T0)
        .i("addi", T1, ZERO, 1)
        .store("sd", ZERO, 0, SP)
        .store("sd", T1, 8, SP)
        .label("loop")
        .load("ld", A0, 0, SP)
        .load("ld", A1, 8, SP)
        .r("add", A2, A0, A1)
        .store("sd", A1, 0, SP)
        .store("sd", A2, 8, SP)
        .i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .load("ld", A0, 0, SP)
        .li(A1, 0)
        .li(A2, 0)
        .exit()
        .finish();
    Program::new(&text, TEXT_BASE, vec![], LOG_RAM, 0)
}

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let program = fibonacci();
    let input = [90, 0, 0, 0];

    // 1. Prove, then onto the wire and back to a receiver.
    let (proof, output, _) = prove(&program, input, &[], MIN_LOG_INV_RATE).expect("the run halts");
    assert_eq!(output, [2_880_067_194_370_816_120, 0, 0, 0]);
    let bytes = bincode::serialize(&proof).unwrap();
    let received: Proof = bincode::deserialize(&bytes).unwrap();
    verify(&program, &input, &output, &received).unwrap();

    // 2. The proof is about this input and this output, and no other.
    let (mut wrong_input, mut wrong_output) = (input, output);
    wrong_input[0] += 1;
    wrong_output[0] += 1;
    assert!(verify(&program, &wrong_input, &output, &received).is_err());
    assert!(verify(&program, &input, &wrong_output, &received).is_err());

    // 3. One proof is one arena phase: the first proof outlives the second's phase.
    let (second, _, _) = prove(&program, input, &[], MIN_LOG_INV_RATE).expect("the run halts");
    verify(&program, &input, &output, &second).unwrap();
    verify(&program, &input, &output, &received).unwrap();
    let stats = zk_alloc::stats();
    assert!(stats.phases >= 2, "expected one phase per proof, got {stats:?}");
    assert!(stats.peak_bytes > 0, "no buffer reached the arena: {stats:?}");
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator: {stats:?}"
    );
}
