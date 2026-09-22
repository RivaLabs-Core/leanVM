import SphincsSecurity.Proof.Fts.RegisteredTargetMonitor
import SphincsSecurity.Proof.Reference.ReferenceSigningReplay

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

theorem OtsVerifierWitness.replay_not_processed_input (key : SecretKey) (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (forgery : Forgery)
    (hagrees : cache.AgreesWithFn f) (hnew : ¬SigningTranscript.Contains log forgery)
    (hreplay : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      evalWithAnswerFn f (signAfterDigest key forgery.signature.randomness (digestIndex digest) (digestLeaves digest)) =
        some forgery.signature) :
    ¬ProcessedMessageInput key (cache, log) (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)) := by
  rintro ⟨message, randomness, response, hentry, hinput, hprocessed⟩
  have hpayload := (tweakableHashInput_injective key.parameter (by trivial) (by trivial) hinput).2
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective key.root hpayload
  have hresult := hprocessed f hagrees
  dsimp only at hresult
  rw [← hrandomness, hreplay] at hresult
  exact hnew ⟨⟨message, response⟩, hentry, hmessage.symm, hresult.symm⟩

/-- Replaying a processed message input rules out a canonical strong forgery, even after signing failed. -/
theorem OtsVerifierWitness.strong_forgery_not_processed_input (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (forgery : Forgery)
    (hagrees : cache.AgreesWithFn f)
    (hnew : ¬SigningTranscript.Contains log forgery)
    (hfull : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      FullyHonestOpening f cache key (digestIndex digest) (digestLeaves digest) forgery.signature)
    (hreference : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      ∀ lay, ReferenceLayerOpening f key (canonicalReferenceWords key f dummy) (referenceTableSelection key f)
        (digestIndex digest) forgery.signature lay) :
    ¬ProcessedMessageInput key (cache, log) (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)) := by
  rintro ⟨message, randomness, response, hentry, hinput, hreplay⟩
  have hpayload := (tweakableHashInput_injective key.parameter (by trivial) (by trivial) hinput).2
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective key.root hpayload
  have hresult := hreplay f hagrees
  dsimp only at hresult
  rw [← hrandomness, honest_signAfterDigest key f dummy cache _ _ forgery.signature hfull hreference] at hresult
  exact hnew ⟨⟨message, response⟩, hentry, hmessage.symm, hresult.symm⟩

theorem RegisteredTargetInvariant.canonical_forgery_registered (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (state : RegisteredTargetState) (forgery : Forgery) (output : HashOutput)
    (hinvariant : RegisteredTargetInvariant key state) (hagrees : state.1.1.AgreesWithFn f)
    (houtput : state.1.1 (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)) = some output)
    (hadmissible : Admissible (truncateMessageDigest output))
    (hnew : ¬SigningTranscript.Contains state.1.2 forgery)
    (hfull : let digest := truncateMessageDigest output
      FullyHonestOpening f state.1.1 key (digestIndex digest) (digestLeaves digest) forgery.signature)
    (hreference : let digest := truncateMessageDigest output
      ∀ lay, OtsVerifierWitness.ReferenceLayerOpening f key (canonicalReferenceWords key f dummy)
        (referenceTableSelection key f) (digestIndex digest) forgery.signature lay) :
    tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness) ∈ state.2 := by
  apply hinvariant.forgery_registered key state forgery output houtput hadmissible
  apply OtsVerifierWitness.strong_forgery_not_processed_input key f dummy state.1.1 state.1.2 forgery hagrees hnew
  · simpa only [hagrees houtput] using hfull
  · simpa only [hagrees houtput] using hreference

theorem RegisteredTargetInvariant.accepted_canonical_forgery_registered (key : SecretKey)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (state : RegisteredTargetState) (forgery : Forgery)
    (hinvariant : RegisteredTargetInvariant key state) (hagrees : state.1.1.AgreesWithFn f)
    (hverify : evalWithAnswerFn f (verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature) = true)
    (hrun : CachedRun state.1.1 f (verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature))
    (hnew : ¬SigningTranscript.Contains state.1.2 forgery)
    (hfull : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      FullyHonestOpening f state.1.1 key (digestIndex digest) (digestLeaves digest) forgery.signature)
    (hreference : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      ∀ lay, OtsVerifierWitness.ReferenceLayerOpening f key (canonicalReferenceWords key f dummy)
        (referenceTableSelection key f) (digestIndex digest) forgery.signature lay) :
    tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness) ∈ state.2 := by
  obtain ⟨digest, heval, hmessage, hadmissible, _⟩ := verify_extract _ _ _ hverify hrun
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hmessage)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness))) = _
    rw [hagrees houtput]
  apply hinvariant.canonical_forgery_registered key f dummy state forgery output hagrees houtput
  · exact hdigest ▸ hadmissible
  · exact hnew
  · simpa only [hagrees houtput] using hfull
  · simpa only [hagrees houtput] using hreference

end SphincsSecurity.Concrete
