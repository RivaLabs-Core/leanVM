import SphincsSecurity.Proof.ConcreteBounds

/-!
# Concrete bounds

The concrete parameter, size and cost claims from `doc/sphincs/main.tex`.
-/

namespace SphincsSecurity.ConcreteBounds

structure Claims : Prop where
  lifetime : signatureLimit = 2 ^ 24
  publicKeyBytes : ∀ key, (serializePublicKey key).length = 32
  secretKeyBytes : ∀ key, (serializeSecretKey key).length = 48
  signatureBytes : ∀ signature, (serializeSignature signature).length = 4924
  verificationCost : verificationHashes = 497
  keyGenerationCost : keyGenerationHashes = 1384448
  signingCost : (191270 : ℚ) < averageSigningHashes ∧ averageSigningHashes < 191271
  cacheSize : publicCacheBytes = 1024

theorem claims : Claims where
  lifetime := Derivation.lifetime
  publicKeyBytes := Derivation.publicKey_size
  secretKeyBytes := Derivation.secretKey_size
  signatureBytes := Derivation.signature_size
  verificationCost := Derivation.verificationHashes_eq
  keyGenerationCost := Derivation.keyGenerationHashes_eq
  signingCost := Derivation.averageSigningHashes_bounds
  cacheSize := Derivation.publicCacheBytes_eq

end SphincsSecurity.ConcreteBounds
