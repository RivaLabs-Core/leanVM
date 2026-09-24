//! One source compiles to one program, always, and the same program it compiled
//! to yesterday.
//!
//! The bytecode digest leads the Fiat--Shamir transcript, so two builds of one
//! source that disagree are two incompatible proof systems, and the symptom is a
//! proof that stops verifying rather than a crash.
//!
//! Two different properties, and only the first is about determinism:
//!
//! * *Within a process*, compiling twice is a real perturbation rather than a
//!   repeat, since `RandomState` bumps its seed once per map, so the second
//!   compilation hashes with different keys than the first.
//! * *Across commits*, `GOLDEN` is a SNAPSHOT of the compiler's output. It does
//!   not prove determinism (nothing iterating a hash container reaches the
//!   bytecode today, and deliberately reversing the branch-output order at a join
//!   moves no digest). It earns its place a different way: a codegen change that
//!   was not intended shows up here and nowhere else, and every entry that moved
//!   this far was a change someone then had to justify.
//!
//! So a moved digest is a question, not a chore: update `GOLDEN` in the same
//! commit and say in the message which change moved it.

use std::collections::BTreeMap;
use std::fs;

use lean_compiler::{compile, parse};
use lean_vm::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "6d0d1243dfe7d79b2a14dd8fee9315dcd43a2b3299d178c4ba72c1e47fd5b6ea"),
    ("const_params", "d0cce752788308077180366e3b2b843b3d155a504f6b38105386deed3661e0a6"),
    ("fibonacci", "d0b940c5ae836a48ab9bda0f60eebf3658bd9f5aaf3d400ff96aa5f894f66fa1"),
    ("hash_heap_chain", "51c441f0d5916728387faea21a8117af369b78ce6e88be5f72e86731db05f42c"),
    ("hash_slices", "34ebec8e70013681561272d86da65256c65d8a4a78069338cf436d963147fa55"),
    ("heapbuf_dyn", "82ef04583242665ac58efb46ff702b7a65cff116ee3a141d30604f8d44696db8"),
    ("hint", "4b7f8565ec37c52a1c810f69332250f41fe03b388f01f92258be2662e4da6352"),
    ("identities", "a0e22f11e6e2261df1192fde3be642210fbea18fe061a99d1150b76736b1b7a6"),
    ("match", "d58e48999b9ade471df74e2aba5768d788631934742f557a1c4b3e0a5ef2de3a"),
    ("match_arms", "e7fd025021a81b0e35645f8e6e6a0bbd6ebc38c5f78772a7e16e842c1c5d308e"),
    ("nested", "5b9426812b6405e1bf5fc60b83f82d9649495fc55bf9a8134dd5ebbb089df7d3"),
    ("runtime_loop", "07631d66263538dfae255e398a47fb357ab7e2f3beb82804647b982917b7130f"),
    ("scoping", "72c5291164da60b20cdfd0cd392c6c7e9e988e5b715a999d6dbf0f3d24e1b241"),
    ("unroll", "361f02cc1a250637ba487fa49a02203225c0295a836addbd57e825fe17469525"),
    ("wots_walk", "c543f4c40f0a2d1d600f3213debac9b1532c22d3d5efafd9a00a4be446f73e7c"),
];

fn digest(p: &Program) -> String {
    primitives::hash::hash(format!("{:?}", p.prog).as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every program in `tests/programs/`, compiled twice.
#[test]
fn bytecode_is_reproducible() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .py programs found");

    let mut actual: Vec<(String, String)> = Vec::new();
    for path in &paths {
        let name = path.file_stem().expect("file stem").to_string_lossy().into_owned();
        let src = fs::read_to_string(path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        let one = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        let two = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        assert_eq!(
            digest(&one),
            digest(&two),
            "{name}: two compilations of one source produced different bytecode, \
             so the compiler is reading a hash seed"
        );
        actual.push((name, digest(&one)));
    }

    let want: BTreeMap<&str, &str> = GOLDEN.iter().copied().collect();
    let moved: Vec<&str> = actual
        .iter()
        .filter(|(n, d)| want.get(n.as_str()) != Some(&d.as_str()))
        .map(|(n, _)| n.as_str())
        .collect();
    let dropped: Vec<&str> = want
        .keys()
        .copied()
        .filter(|n| !actual.iter().any(|(a, _)| a == n))
        .collect();
    assert!(
        dropped.is_empty(),
        "GOLDEN names a program that no longer exists: {dropped:?}"
    );
    if !moved.is_empty() {
        let table: String = actual
            .iter()
            .map(|(n, d)| format!("    (\"{n}\", \"{d}\"),\n"))
            .collect();
        panic!("bytecode changed for {moved:?}\n\nif that was intended, GOLDEN is now:\n{table}");
    }
}
