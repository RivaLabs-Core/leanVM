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
    ("conditionals", "90d67c1546f3a31e4aaa5c671fd459109b5d5ed94f89f33d2c7938c193ca4c45"),
    ("const_params", "a3410c606609efbd9ed499d46b8efcdf44d6e4c19fb3f86425166c9781710d3b"),
    ("fibonacci", "9ca8531e7515fa728660eb2337aee1caf664ee62e581718de18b18aff73c33cb"),
    ("hash_heap_chain", "dff4ba70a4078a485dce0686707d2935e77997eb98f3bbb062131597885c403f"),
    ("hash_slices", "3bb96bbda4b8af4eebca0a943f54a43e43f68974d633e25153f3d79f256b748e"),
    ("heapbuf_dyn", "ba94f64ede1f46bf48d572d6061d49a18ed2b0a6c4b3af9a7636eac2a972220f"),
    ("hint", "df2f2726b782471a1de07c609d8c5be84872ccd6b7c200cf74cc3e6ddd9fd367"),
    ("identities", "df1446b844c0b623b08e9acab2eb900bdc97f77bc1a07c3baaa4e3993ed7aa9b"),
    ("match", "91b7e2b511681bdd0ef7b1e34953194aad5ec93c11ab466d37abd06ba9ae3ec2"),
    ("match_arms", "c8a92bf0e636e663f4a06842dd97d68940f9123acd9c1c7f0dc42d8001a46216"),
    ("nested", "00d1b25b1e235fcee0ba1561d823bc26493a6a3d0ac17c52c13bfdd62b939cc0"),
    ("runtime_loop", "83b820ee574d256d1c689257e305c5f5ae48040f410f7dbc803dc8b73cca0906"),
    ("scoping", "a87869698d9ef330f987dd93cf615884eac3fcc1c9f0be039c8df00c4af92e72"),
    ("unroll", "017565ebc4ba0f7e563387e43533bcdedcbd5ef916397a143a667a6d6dc78e5d"),
    ("wots_walk", "fada2fac6b712cd7739047c654328480850a8acc250086f48ef534f3e43876a6"),
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
