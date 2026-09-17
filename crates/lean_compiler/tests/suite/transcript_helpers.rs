//! The Fiat-Shamir helper shape: nested `@inline` functions passing a four-cell
//! state and a three-cell scalar as runs, absorbing the scalar into a compression
//! through a list literal that flattens the run, and returning both the next
//! state and a three-cell challenge sliced out of it.

use lean_compiler::{compile, parse};
use lean_vm::vmhash::compress;
use primitives::field::F64;

#[test]
fn transcript_helpers_are_ordinary_nested_inline_zkdsl() {
    let src = r#"
from snark_lib import *

@inline
def absorb(state, scalar):
    out = StackBuf(4)
    blake2s(state, [scalar, 13], out)
    return out

@inline
def squeeze(state):
    return state[0:3]

@inline
def observe(state, scalar):
    fresh = absorb(state, scalar)
    challenge = squeeze(fresh)
    return fresh, challenge

def main():
    state = [1, 2, 3, 4]
    scalar = [5, 6, 7]
    s, c = observe(state, scalar)
    p = GEN ** 0
    p[0:3] = c
    p[GEN ** 3] = s[3]
    return
"#;
    let program = compile(&parse(src).expect("parse transcript helpers"));
    let d = compress([1, 2, 3, 4].map(F64), [5, 6, 7, 13].map(F64));
    let want = d;
    assert!(program.execute(want).unconstrained_reads.is_empty());

    let mut bad = want;
    bad[2] += F64::ONE;
    assert!(
        std::panic::catch_unwind(|| program.execute(bad)).is_err(),
        "the challenge's top limb is bound"
    );
}
