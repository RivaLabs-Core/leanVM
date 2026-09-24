//! A fused dispatch (`match` whose arms all call one function) shares one callee
//! frame, allocated before the jump. Its size is the arm the scrutinee selects,
//! not the largest arm's: frame addresses are prover-chosen, so this is witness
//! generation only, and it keeps a short walk from paying a long walk's memory.

use lean_compiler::{compile, compile_without_filler, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::F192;

fn program(digit: usize) -> String {
    format!(
        "\
def walk(value, k: Const):
    word = value
    for s in unroll(k, 15):
        out = StackBuf(13)
        sha3([word, 0], [0, 0], out)
        word = out[0]
    return word

def main():
    d = GEN ** {digit}
    assert log(d) < 16
    x = match(log(d), range(0, 16), lambda k: walk(GEN ** 3, k))
    p = 1
    p[1] = 0
    p[GEN] = 0
    return
"
    )
}

#[test]
fn a_dispatched_frame_is_sized_for_the_arm_taken() {
    let mem = |digit: usize| {
        compile_without_filler(&parse(&program(digit)).expect("parse"))
            .execute([F192::ZERO; 2])
            .mem_used
    };
    let used: Vec<usize> = [0, 7, 14, 15].into_iter().map(mem).collect();
    assert!(
        used.windows(2).all(|w| w[0] > w[1]),
        "memory must shrink with the walk: {used:?}"
    );
    // Each step is a 13-cell state; the empty arm keeps nothing of the longest.
    assert!(used[0] - used[3] >= 15 * 13, "{used:?}");
    for digit in [0, 15] {
        let p = compile(&parse(&program(digit)).expect("parse"));
        let (proof, _) = prove(&p, [F192::ZERO; 2], lean_vm::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&p, &[F192::ZERO; 2], &proof).expect("an exact-size frame proves");
    }
}
