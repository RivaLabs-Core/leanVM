import SphincsSecurity.Completeness.Code
import SphincsSecurity.Proof.Scheme.Bytes

/-!
# Concrete bound derivations

The size proofs count the specified serializations. The cost proofs count one call to the hash
function, independently of the input length. The signing average uses the exact target-sum code
size and the public top-tree cache implemented by `crates/sphincs`.
-/

open scoped BigOperators

namespace SphincsSecurity.ConcreteBounds

open Concrete Completeness

def serializePublicKey (key : PublicKey) : List UInt8 :=
  bytesLE 16 key.root ++ bytesLE 16 key.parameter

def serializeSecretKey (key : Seeded.SecretKey) : List UInt8 :=
  bytesLE 16 key.parameter ++ bytesLE 32 key.seed

def serializeFtsOpening (signature : Signature) (tree : FtsTree) : List UInt8 :=
  bytesLE 16 (signature.ftsSecret tree) ++
    (List.ofFn fun level : Fin ftsTreeHeight => bytesLE 16 (signature.ftsPath tree level)).flatten

def serializeLayer (signature : Signature) (lay : Layer) : List UInt8 :=
  bytesLE 4 (signature.layers lay).counter ++
    (List.ofFn fun chain : ChainIndex => bytesLE 16 ((signature.layers lay).chainValues chain)).flatten ++
    (List.ofFn fun level : Fin (layerHeight lay) => bytesLE 16 ((signature.layers lay).path level)).flatten

def serializeSignature (signature : Signature) : List UInt8 :=
  bytesLE 16 signature.randomness ++
    (List.ofFn (serializeFtsOpening signature)).flatten ++
    (List.ofFn (serializeLayer signature)).flatten

def oneTimeLeafHashes : Nat := numChains + numChains * (chainLength - 1) + 1

def fullTreeHashes (height : Nat) : Nat := 2 ^ height * oneTimeLeafHashes + (2 ^ height - 1)

def keyGenerationHashes : Nat := 1 + fullTreeHashes (layerHeight topLayer)

def verificationHashes : Nat :=
  1 + ((ftsTrees - 1) * (ftsTreeHeight + 1) + 1) +
    numLayers * (1 + (numChains * (chainLength - 1) - targetSum) + 1) + totalHeight

def cacheSplitHeight : Nat := (layerHeight topLayer + 1) / 2

def publicCacheEntries : Nat := 2 ^ (layerHeight topLayer - cacheSplitHeight)

def publicCacheBytes : Nat := publicCacheEntries * (digestBits / 8)

def cachedTopTreeHashes : Nat :=
  fullTreeHashes cacheSplitHeight + (publicCacheEntries - 1)

def fewTimeSigningHashes : Nat :=
  (ftsTrees - 1) * (3 * 2 ^ ftsTreeHeight - 1) + 1

def oneTimeSigningHashes : Nat := numChains + targetSum

def signingTreeHashes : Nat :=
  cachedTopTreeHashes + ∑ lay : Layer, if lay = topLayer then 0 else fullTreeHashes (layerHeight lay)

def signingFixedHashes : Nat :=
  2 * 2 ^ ftsTreeHeight + fewTimeSigningHashes +
    numLayers * oneTimeSigningHashes + signingTreeHashes

noncomputable def averageEncodingTrials : ℚ :=
  (2 ^ digestBits : ℚ) / codeCount targetSum

noncomputable def averageSigningHashes : ℚ :=
  signingFixedHashes + numLayers * averageEncodingTrials

namespace Derivation

theorem targetSumCodewords :
    codeCount targetSum = 27362001415540541846731060490886528 := by
  rw [codeCount_target, weight_eq]
  decide

theorem publicKey_size (key : PublicKey) :
    (serializePublicKey key).length = 32 := by
  simp [serializePublicKey, bytesLE_length]

theorem secretKey_size (key : Seeded.SecretKey) :
    (serializeSecretKey key).length = 48 := by
  simp [serializeSecretKey, bytesLE_length]

theorem flatten_ofFn_length {n m : Nat} {α : Type} (parts : Fin n → List α)
    (h : ∀ i, (parts i).length = m) : (List.ofFn parts).flatten.length = n * m := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  simp [h]

theorem serializeFtsOpening_length (signature : Signature) (tree : FtsTree) :
    (serializeFtsOpening signature tree).length = 176 := by
  rw [serializeFtsOpening, List.length_append, bytesLE_length,
    flatten_ofFn_length _ (fun _ => bytesLE_length 16 _)]
  norm_num [ftsTreeHeight]

theorem serializeLayer_length (signature : Signature) (lay : Layer) :
    (serializeLayer signature lay).length = 676 + 16 * layerHeight lay := by
  rw [serializeLayer, List.length_append, List.length_append, bytesLE_length,
    flatten_ofFn_length _ (fun _ => bytesLE_length 16 _),
    flatten_ofFn_length _ (fun _ => bytesLE_length 16 _)]
  norm_num [numChains, Nat.mul_comm]

theorem signature_size (signature : Signature) :
    (serializeSignature signature).length = 4924 := by
  rw [serializeSignature, List.length_append, List.length_append, bytesLE_length,
    flatten_ofFn_length _ (serializeFtsOpening_length signature), List.length_flatten]
  rw [List.map_ofFn]
  dsimp only [Function.comp_def]
  simp_rw [serializeLayer_length]
  decide

theorem keyGenerationHashes_eq : keyGenerationHashes = 1384448 := by
  norm_num [keyGenerationHashes, fullTreeHashes, oneTimeLeafHashes, layerHeight, topLayer,
    numChains, chainLength, winternitzBits, maxLayerHeight]

theorem verificationHashes_eq : verificationHashes = 497 := by
  norm_num [verificationHashes, ftsTrees, ftsTreeHeight, numLayers, numChains, chainLength,
    winternitzBits, targetSum, totalHeight]

theorem publicCacheBytes_eq : publicCacheBytes = 1024 := by
  norm_num [publicCacheBytes, publicCacheEntries, cacheSplitHeight, layerHeight, topLayer,
    maxLayerHeight, digestBits]

theorem signingTreeHashes_eq : signingTreeHashes = 108220 := by
  decide

theorem averageSigningHashes_bounds :
    (191270 : ℚ) < averageSigningHashes ∧ averageSigningHashes < 191271 := by
  rw [averageSigningHashes, averageEncodingTrials, targetSumCodewords, signingFixedHashes,
    signingTreeHashes_eq]
  norm_num [fewTimeSigningHashes, oneTimeSigningHashes, numLayers, ftsTrees, ftsTreeHeight,
    numChains, targetSum, digestBits]

theorem lifetime : signatureLimit = 2 ^ 24 := by rfl

end Derivation

end SphincsSecurity.ConcreteBounds
