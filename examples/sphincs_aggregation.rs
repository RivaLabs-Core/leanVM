//! Aggregate a handful of SPHINCS+ signatures into one proof, then verify it.
//!
//! ```sh
//! cargo run --release --example sphincs_aggregation
//! ```

use leanvm::*;

const N_SIGNERS: usize = 8;
const LOG_INV_RATE: usize = 2;

fn main() {
    setup_prover();
    let rng = &mut rand::rng();

    let signatures: Vec<_> = (0..N_SIGNERS)
        .map(|i| {
            let (secret_key, public_key) = sphincs::key_gen(rng);
            let message = [i as u8; sphincs::MESSAGE_LEN];
            let signature = sphincs::sign(&secret_key, &message);
            sphincs::verify(&public_key, &message, &signature).unwrap();
            (public_key, message, signature)
        })
        .collect();

    let proof = aggregate(&[], vec![], signatures, &[], None, LOG_INV_RATE).unwrap();

    let bytes = proof.to_bytes();
    let received = EthereumProof::from_bytes(&bytes).unwrap();
    received.verify().unwrap(); // verify the snark is valid

    println!(
        "{} SPHINCS+ signatures ({} x {} bytes = {}) aggregated into a {}-byte proof",
        received.sphincs_signers().len(),
        received.sphincs_signers().len(),
        sphincs::SIG_SIZE,
        bytes.len()
    );
}
