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
    ("conditionals", "6a1ef19ac5e5d94b35f534351a9d9dfde572e370cbcf5100ab325f276bdd80e0"),
    ("const_params", "81b5502efc8ab32738c119fdde90a971b07d5bea2914b634eceb03d4a6ee5d33"),
    ("fibonacci", "aa209603fe71e4b8f322c9cca7a632f9659da8565077b798a3a52b1819551b24"),
    ("hash_heap_chain", "9b2df8aeeef61d26cae759b29cd0fd8bdcb1f7a8ee5b7326987a4b47854363df"),
    ("hash_slices", "317fa9a020d3edfe09f2acec4210898886f97d348e097b1e8d48ec2983039b68"),
    ("heapbuf_dyn", "fe2c06694cb7b93267cdff9f045700591a35e4d540587f7178eb5e88d74bb211"),
    ("hint", "5728813cbaa17ba91235673a692ee2b861460e1f70c2f6a91fa8f1a664167f3c"),
    ("identities", "48fc9ccbf94c4ca3957e1a41eb7e02d4e61a42194af53f2a2d83b90ce6b4f0ee"),
    ("match", "2d6dcbd325d4f8c988c83977d2b0685c964571e2e50801dbf1185f5badd6d962"),
    ("match_arms", "a824fccbeb458f716520da1b3b3798dacdc592ae0cd6e32e72cc3d5242ee6b25"),
    ("nested", "1c9efdbb2bc881f4688714207cae102e50f9a120ee23fcb28a93539b2b7f20d9"),
    ("runtime_loop", "ba2b3cc06b823521fd08ef47660349593faa207af2f144abaddf5a076ac3e63e"),
    ("scoping", "5da1ffb57966345dc02143bf2505ecb6e892b33859d96447d6a9fef9bf68b85c"),
    ("unroll", "c297a1290ecf61332f3bdd7c5b63bbad7bc016917cf1736c3564b29388d6c034"),
    ("wots_walk", "739ede4e4feb4f93d7a29238ee4213e4093a3b5e9260ed243a718c93e1704eca"),
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
