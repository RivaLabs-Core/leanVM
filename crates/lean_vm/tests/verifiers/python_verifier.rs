//! Pins `python-verifier/verifier.py` against `lean_vm::cpu::verify`: the same
//! protocol is written out in Rust and in Python, so any protocol change must land
//! in both, and this is what catches the Python one drifting.

use fiat_shamir::transcript::RawProof;
use lean_vm::cpu::{prove, verify, verify_to_raw};
use primitives::field::F64;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Instant;

/// One statement laid out the way the Python verifier takes it: the bytecode
/// multilinear plus four public words, not a structured program.
pub struct PythonStatement {
    directory: PathBuf,
    bytecode: PathBuf,
    public_input: PathBuf,
}

impl PythonStatement {
    pub fn new(tag: &str, program: &lean_vm::cpu::Program, public_input: &[F64; 4]) -> Self {
        let directory = std::env::temp_dir().join(format!("leanvm-python-verifier-{tag}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("create test directory");
        let statement = Self {
            bytecode: directory.join("bytecode.bin"),
            public_input: directory.join("public_input.bin"),
            directory,
        };
        let table: Vec<u8> = lean_vm::cpu::layout::bytecode_table(&program.prog)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(&statement.bytecode, &table).expect("write bytecode");
        let pi: Vec<u8> = public_input.iter().flat_map(|w| w.0.to_le_bytes()).collect();
        std::fs::write(&statement.public_input, &pi).expect("write public input");
        statement
    }

    /// Write `raw` as the two files Python reads and run the verifier on it: the
    /// scalar stream as 24-byte little-endian elements, and every opening's leaf
    /// words followed by its sibling digests. Neither file carries a length, the
    /// reader deriving every leaf width and tree height from the protocol it is
    /// replaying.
    pub fn verify(&self, raw: &RawProof) -> Output {
        let mut stream = Vec::new();
        for scalar in &raw.stream {
            for limb in [scalar.c0, scalar.c1, scalar.c2] {
                stream.extend(limb.to_le_bytes());
            }
        }
        let mut openings = Vec::new();
        for opening in &raw.merkle {
            for word in &opening.leaf_data {
                openings.extend(word.0.to_le_bytes());
            }
            for digest in &opening.path {
                openings.extend(digest);
            }
        }
        let stream_path = self.directory.join("stream.bin");
        let openings_path = self.directory.join("merkle_openings.bin");
        std::fs::write(&stream_path, stream).expect("write scalar stream");
        std::fs::write(&openings_path, openings).expect("write Merkle openings");
        Command::new("python3")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py"))
            .arg(&self.bytecode)
            .arg(&self.public_input)
            .arg(stream_path)
            .arg(openings_path)
            .output()
            .expect("run native Python verifier")
    }

    pub fn assert_accepts(&self, raw: &RawProof) {
        let output = self.verify(raw);
        assert!(
            output.status.success(),
            "native Python verification failed:\n{}",
            String::from_utf8_lossy(&output.stderr),
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "verification succeeded");
    }
}

impl Drop for PythonStatement {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

/// Both verifiers reject a proof whose announcement or commitment root is not a
/// canonical encoding, and agree on everything before that.
#[test]
fn test_python_verifier() {
    let (program, public_input) = super::read_write::fibonacci();
    let (proof, stats) = prove(&program, public_input, 1);
    // Python reads the RAW proof: same protocol, each query carrying its own
    // full Merkle path instead of one octopus over the batch. A Rust verify
    // expands the wire form, so the pruning is written once.
    let raw = verify_to_raw(&program, &public_input, &proof).expect("honest proof verifies");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    let statement = PythonStatement::new("tamper", &program, &public_input);
    let verification_started = Instant::now();
    statement.assert_accepts(&raw);
    let verification_time = verification_started.elapsed();

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert!(verify(&program, &public_input, &malformed_announcement).is_err());
    let mut raw_announcement = raw.clone();
    raw_announcement.stream[0].c1 = 1;
    let output = statement.verify(&raw_announcement);
    assert!(!output.status.success(), "Python accepted a noncanonical announcement");

    let mut malformed_root = proof.clone();
    // Past the announcement: the memory size, the table heights, the rate, the final clock.
    let root_offset = lean_vm::tables::N_TABLES + 3;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(verify(&program, &public_input, &malformed_root).is_err());
    let mut raw_root = raw.clone();
    raw_root.stream[root_offset].c2 = 1;
    let output = statement.verify(&raw_root);
    assert!(
        !output.status.success(),
        "Python accepted a noncanonical commitment root"
    );

    println!(
        "{} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.prog.len(),
        stats.cycles,
        encoded.len(),
        verification_time,
    );
}
