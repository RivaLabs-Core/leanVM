import SphincsSecurity.Statement

/-!
# The one-attempt encoding interface

The one-time-signature proof was written for an encoding searched over counters. The checksum encoding needs no search, so the proof instantiates that interface with a single attempt and a zero-width counter, and the lemmas at the end identify it with the counter-free algorithms of the statement.
-/

namespace SphincsSecurity

/-- Sealed so that the kernel does not see that decoding always succeeds: otherwise it may evaluate whole signing runs while checking proofs about them. -/
opaque Checksum.decodeDigestSealed :
    {decode : Digest → Option Encoding // decode = fun digest => some (Checksum.encode digest)} :=
  ⟨_, rfl⟩

/-- The encoding as a decoder that never fails. -/
def Checksum.decodeDigest (digest : Digest) : Option Encoding := Checksum.decodeDigestSealed.1 digest

theorem Checksum.decodeDigest_eq (digest : Digest) : Checksum.decodeDigest digest = some (Checksum.encode digest) :=
  congrFun Checksum.decodeDigestSealed.2 digest

def encodingAttemptLimit : Nat := 1
def counterBits : Nat := 0
abbrev Counter := BitVec counterBits

abbrev LayerSignature.counter {lay : Layer} (_part : LayerSignature lay) : Counter := 0

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def encodeAttempt (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf) (bytesLE 16 message ++ bytesLE 0 counter)
  return Checksum.decodeDigest digest

def otsLeafAttempt (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encodeAttempt parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-- Run layers from bottom to top, stopping at the first failure. -/
def sequenceLayersOpt {α : Layer → Type}
    (computation : (lay : Layer) → m (Option (α lay))) : m (Option ((lay : Layer) → α lay)) := do
  let some bottom ← computation bottomLayer | return none
  let some middle ← computation middleLayer | return none
  let some top ← computation topLayer | return none
  return some (Fin.cases top (Fin.cases middle (Fin.cases bottom (fun i => Fin.elim0 i))))

variable [LawfulMonad m]

theorem encodeAttempt_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    encodeAttempt (m := m) parameter lay tree leaf message counter = some <$> encode parameter lay tree leaf message := by
  simp only [encodeAttempt, encode, map_bind, map_pure, Checksum.decodeDigest_eq]
  congr 2

theorem otsLeafAttempt_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    otsLeafAttempt (m := m) parameter lay tree leaf message counter values =
      some <$> otsLeaf parameter lay tree leaf message values := by
  simp only [otsLeafAttempt, encodeAttempt_eq, otsLeaf, bind_map_left, map_bind, bind_pure_comp]

omit [HasQuery HashSpec m] in
theorem sequenceLayersOpt_some {α : Layer → Type} (computation : (lay : Layer) → m (α lay)) :
    sequenceLayersOpt (fun lay => some <$> computation lay) = some <$> sequenceLayers computation := by
  simp only [sequenceLayersOpt, sequenceLayers, bind_map_left, map_bind, map_pure]

end Concrete

end SphincsSecurity
