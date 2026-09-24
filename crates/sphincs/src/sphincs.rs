//! The hypertree and the three algorithms: `d = 5` layers of height-4 Merkle
//! trees over WOTS+ keys, layer 0 signing the FORS key the message digest
//! picks, the top layer's single root being the public key.
//!
//! The digest `H_msg` names a hypertree leaf `htIdx` and the FORS indices, so a
//! key answers for all `2^h` leaves with nothing reserved or spent: the scheme
//! is stateless.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

/// `(pkRoot, pkSeed)`. Ordered lexicographically on [`Self::flatten`], which is
/// what an aggregate's signer list is sorted and deduplicated by. The on-chain
/// form is two `bytes32`, each value top-aligned (`v ‖ 0^16`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SphincsPublicKey {
    pub root: Digest,
    pub public_param: PublicParam,
}

impl SphincsPublicKey {
    pub fn flatten(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }

    pub fn from_bytes(bytes: &[u8; PUB_KEY_SIZE]) -> Self {
        Self {
            root: bytes[..N].try_into().unwrap(),
            public_param: bytes[N..].try_into().unwrap(),
        }
    }

    /// The verifier's `(pkSeed, pkRoot)` arguments. Always canonical (low 128
    /// bits zero), which the EVM verifier requires.
    pub fn to_bytes32(&self) -> ([u8; 32], [u8; 32]) {
        (word(&self.public_param), word(&self.root))
    }
}

/// The three seeds. The root is derived (the top layer's tree, `2^h'` WOTS keys).
#[derive(Clone)]
pub struct SphincsSecretKey {
    pub public_param: PublicParam,
    pub root: Digest,
    sk_seed: [u8; N],
    sk_prf: [u8; N],
}

impl std::fmt::Debug for SphincsSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SphincsSecretKey")
            .field("public_param", &self.public_param)
            .field("root", &self.root)
            .finish_non_exhaustive()
    }
}

impl SphincsSecretKey {
    /// SECRET KEY MATERIAL: `SK.seed ‖ SK.prf ‖ PK.seed`.
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_SIZE] {
        let mut out = [0; SECRET_KEY_SIZE];
        out[..N].copy_from_slice(&self.sk_seed);
        out[N..2 * N].copy_from_slice(&self.sk_prf);
        out[2 * N..].copy_from_slice(&self.public_param);
        out
    }

    /// Inverse of [`Self::to_bytes`]; rebuilds the root.
    pub fn from_bytes(bytes: &[u8; SECRET_KEY_SIZE]) -> Self {
        let part = |i: usize| bytes[i * N..(i + 1) * N].try_into().unwrap();
        key_gen_from_seeds(part(0), part(1), part(2)).0
    }

    pub fn public_key(&self) -> SphincsPublicKey {
        SphincsPublicKey {
            root: self.root,
            public_param: self.public_param,
        }
    }
}

/// One hypertree layer of a signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HtLayer {
    /// `σ`: chain `i` at position `digit_i`.
    pub chains: [Digest; L],
    /// The Merkle authentication path, bottom first.
    pub path: [Digest; SUBTREE_H],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsSignature {
    /// `R`.
    pub randomizer: Randomizer,
    /// One opened leaf secret per FORS tree.
    pub fors_secrets: [Digest; K],
    /// Each tree's authentication path, bottom first.
    pub fors_paths: [[Digest; A]; K],
    /// Layer 0 first.
    pub layers: [HtLayer; D],
}

impl SphincsSignature {
    /// The verifier's blob, exactly [`SIG_SIZE`] bytes: `R ‖ k secrets ‖ k·a path
    /// nodes ‖ d × [l chains ‖ h' path nodes]`.
    pub fn to_bytes(&self) -> [u8; SIG_SIZE] {
        let mut out = [0; SIG_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        put(&self.randomizer);
        self.fors_secrets.iter().for_each(|s| put(s));
        self.fors_paths.iter().flatten().for_each(|s| put(s));
        for layer in &self.layers {
            layer.chains.iter().for_each(|s| put(s));
            layer.path.iter().for_each(|s| put(s));
        }
        debug_assert_eq!(at, SIG_SIZE);
        out
    }

    pub fn from_bytes(bytes: &[u8; SIG_SIZE]) -> Self {
        let at = std::cell::Cell::new(0);
        let take = |len: usize| {
            let s = &bytes[at.get()..at.get() + len];
            at.set(at.get() + len);
            s
        };
        let digest = || -> Digest { take(N).try_into().unwrap() };
        let randomizer = digest();
        let fors_secrets = std::array::from_fn(|_| digest());
        let fors_paths = std::array::from_fn(|_| std::array::from_fn(|_| digest()));
        let layers = std::array::from_fn(|_| {
            let chains = std::array::from_fn(|_| digest());
            let path = std::array::from_fn(|_| digest());
            HtLayer { chains, path }
        });
        debug_assert_eq!(at.get(), SIG_SIZE);
        Self {
            randomizer,
            fors_secrets,
            fors_paths,
            layers,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SphincsVerifyError {
    /// The hypertree walk does not reach the key's root: the only way a
    /// well-formed signature fails, there being no grinding predicate to check.
    RootMismatch,
}

impl std::fmt::Display for SphincsVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RootMismatch => write!(f, "the hypertree walk does not reach the key's root"),
        }
    }
}

impl std::error::Error for SphincsVerifyError {}

/// `(tree, leaf)` on layer `layer` of hypertree leaf `ht_idx`.
pub fn ht_position(ht_idx: u32, layer: usize) -> (u64, u32) {
    let below = ht_idx >> (layer * SUBTREE_H);
    (u64::from(below >> SUBTREE_H), below & ((1 << SUBTREE_H) - 1))
}

/// `Gen` on a fresh key: the three seeds come from `rng`.
pub fn key_gen(rng: &mut impl CryptoRng) -> (SphincsSecretKey, SphincsPublicKey) {
    key_gen_from_seeds(rng.random(), rng.random(), rng.random())
}

/// Deterministic `Gen` from seed material: `keccak256(tag ‖ material)[..16]` for
/// each seed, `tag` one of `"SPHINCS-v2 SK.seed"`, `"SPHINCS-v2 SK.prf"`,
/// `"SPHINCS-v2 PK.seed"`. (Signer-private: any derivation of three independent
/// seeds serves.)
pub fn key_gen_from_seed(material: MasterSecret) -> (SphincsSecretKey, SphincsPublicKey) {
    let seed = |tag: &[u8]| truncate(&primitives::hash::keccak256(&[tag, &material].concat()));
    key_gen_from_seeds(
        seed(b"SPHINCS-v2 SK.seed"),
        seed(b"SPHINCS-v2 SK.prf"),
        seed(b"SPHINCS-v2 PK.seed"),
    )
}

/// `Gen` on given seeds, the reference signer's `keygen`.
pub fn key_gen_from_seeds(
    sk_seed: [u8; N],
    sk_prf: [u8; N],
    public_param: PublicParam,
) -> (SphincsSecretKey, SphincsPublicKey) {
    let root = subtree_levels(&public_param, &sk_seed, (D - 1) as u32, 0)[SUBTREE_H][0];
    let sk = SphincsSecretKey {
        public_param,
        root,
        sk_seed,
        sk_prf,
    };
    let pk = sk.public_key();
    (sk, pk)
}

/// Sign. Deterministic and stateless.
pub fn sign(sk: &SphincsSecretKey, message: &Message) -> SphincsSignature {
    let pp = &sk.public_param;
    let randomizer = randomizer(&sk.sk_prf, message);
    let d = h_msg(pp, &sk.root, &randomizer, message);
    let ht_idx = ht_index(&d);
    let (fors_secrets, fors_paths, fors_pk) = fors_sign(pp, &sk.sk_seed, ht_idx, &fors_indices(&d));

    let mut node = fors_pk;
    let layers = std::array::from_fn(|layer| {
        let (tree, leaf) = ht_position(ht_idx, layer);
        let chains = wots_sign(pp, &sk.sk_seed, layer as u32, tree, leaf, &node);
        let levels = subtree_levels(pp, &sk.sk_seed, layer as u32, tree);
        node = levels[SUBTREE_H][0];
        HtLayer {
            chains,
            path: auth_path(&levels, leaf),
        }
    });
    debug_assert_eq!(node, sk.root);

    SphincsSignature {
        randomizer,
        fors_secrets,
        fors_paths,
        layers,
    }
}

/// Everything a verification computes on the way to the root, for provers that
/// replay it: the digest, what it selects, and what each layer signs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyTrace {
    pub digest: [u8; 32],
    pub ht_idx: u32,
    pub fors_indices: [u32; K],
    /// `signed[layer]`: the node layer `layer`'s WOTS key signs (the FORS key on
    /// layer 0); `signed[d]` is the root reached.
    pub signed: [Digest; D + 1],
    /// Each layer's WOTS digits, the checksum's last.
    pub digits: [[u8; L]; D],
}

/// Replay a verification up to the root comparison.
pub fn verify_trace(pk: &SphincsPublicKey, message: &Message, signature: &SphincsSignature) -> VerifyTrace {
    let pp = &pk.public_param;
    let digest = h_msg(pp, &pk.root, &signature.randomizer, message);
    let indices = fors_indices(&digest);
    let ht_idx = ht_index(&digest);
    let mut signed = [[0; N]; D + 1];
    let mut digits_of = [[0; L]; D];
    signed[0] = fors_pk_from_sig(pp, ht_idx, &indices, &signature.fors_secrets, &signature.fors_paths);
    for (layer, sig) in signature.layers.iter().enumerate() {
        let (tree, leaf) = ht_position(ht_idx, layer);
        digits_of[layer] = digits(&wots_digest(pp, layer as u32, tree, leaf, &signed[layer]));
        let wots_pk = wots_pk_from_sig(pp, layer as u32, tree, leaf, &signed[layer], &sig.chains);
        signed[layer + 1] = tree_fold(pp, layer as u32, tree, leaf, wots_pk, &sig.path);
    }
    VerifyTrace {
        digest,
        ht_idx,
        fors_indices: indices,
        signed,
        digits: digits_of,
    }
}

/// `Ver`, `SphincsVerifier_v2.verify` on the signature's blob.
pub fn verify(
    pk: &SphincsPublicKey,
    message: &Message,
    signature: &SphincsSignature,
) -> Result<(), SphincsVerifyError> {
    if verify_trace(pk, message, signature).signed[D] == pk.root {
        Ok(())
    } else {
        Err(SphincsVerifyError::RootMismatch)
    }
}
