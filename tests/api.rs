use leanvm::asm::*;
use leanvm::*;

const STEPS: u64 = 1000;

/// Fibonacci mod 2^64, and the output it proves: `a0 = F(STEPS)`.
fn fibonacci() -> (Program, [u64; 4]) {
    let text = Asm::new()
        .li(A0, 0)
        .li(A1, 1)
        .li(T0, STEPS / 2)
        .label("loop")
        .r("add", A0, A0, A1)
        .r("add", A1, A0, A1)
        .i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .li(A1, 0)
        .exit()
        .finish();
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..STEPS / 2 {
        a = a.wrapping_add(b);
        b = b.wrapping_add(a);
    }
    (Program::new(&text, TEXT_BASE, vec![], 0), [a, 0, 0, 0])
}

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let (program, expected) = fibonacci();

    // 1. Prove, then onto the wire and back to a receiver.
    let (proof, output, _) = prove(&program, MIN_LOG_INV_RATE).expect("the run halts");
    assert_eq!(output, expected);
    let bytes = bincode::serialize(&proof).unwrap();
    let received: Proof = bincode::deserialize(&bytes).unwrap();
    verify(&program, &output, &received).unwrap();

    // 2. The proof is about this output and no other.
    let mut wrong_output = output;
    wrong_output[0] += 1;
    assert!(verify(&program, &wrong_output, &received).is_err());

    // 3. One proof is one arena phase: the first proof outlives the second's phase.
    let (second, _, _) = prove(&program, MIN_LOG_INV_RATE).expect("the run halts");
    verify(&program, &output, &second).unwrap();
    verify(&program, &output, &received).unwrap();
    let stats = zk_alloc::stats();
    assert!(stats.phases >= 2, "expected one phase per proof, got {stats:?}");
    assert!(stats.peak_bytes > 0, "no buffer reached the arena: {stats:?}");
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator: {stats:?}"
    );
}
