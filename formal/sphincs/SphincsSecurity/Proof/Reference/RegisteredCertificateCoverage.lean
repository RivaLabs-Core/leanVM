import SphincsSecurity.Proof.Reference.RegisteredForgerySource
import SphincsSecurity.Proof.Fts.RegisteredCertificateBound
import SphincsSecurity.Proof.Fts.RegisteredLedgerCoverage

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A canonical strong forgery with the required FTS certificate in the final cache. -/
def RegisteredCanonicalCertificate (key : SecretKey) (dummy : OtsReferenceWords) (required : Finset FtsTree)
    (result : Forgery × RegisteredTargetState) : Prop :=
  ¬SigningTranscript.Contains result.2.1.2 result.1 ∧
    ∃ f : QueryImpl HashSpec Id, result.2.1.1.AgreesWithFn f ∧
      let input := tweakableHashInput key.parameter .message
        (messageDigestPayload key.root result.1.message result.1.signature.randomness)
      let digest := truncateMessageDigest (f input)
      (∃ witnessCache, FullyHonestOpening f witnessCache key (digestIndex digest) (digestLeaves digest) result.1.signature) ∧
        (∀ lay, OtsVerifierWitness.ReferenceLayerOpening f key (canonicalReferenceWords key f dummy)
          (referenceTableSelection key f) (digestIndex digest) result.1.signature lay) ∧
        TargetCertificateAt key required result.2.1 input

theorem RegisteredCanonicalCertificate.registered (key : SecretKey) (dummy : OtsReferenceWords)
    (required : Finset FtsTree) (result : Forgery × RegisteredTargetState)
    (hinvariant : RegisteredTargetInvariant key result.2)
    (hcertificate : RegisteredCanonicalCertificate key dummy required result) :
    ∃ input ∈ result.2.2, TargetCertificateAt key required result.2.1 input := by
  obtain ⟨hnew, f, hagrees, hfull, hreference, hcertificate⟩ := hcertificate
  refine ⟨_, ?_, hcertificate⟩
  obtain ⟨output, houtput, _, hadmissible, _⟩ := hcertificate
  apply hinvariant.forgery_registered key result.2 result.1 output houtput hadmissible
  apply OtsVerifierWitness.replay_not_processed_input key f result.2.1.1 result.2.1.2 result.1 hagrees hnew
  obtain ⟨witnessCache, hfull⟩ := hfull
  exact OtsVerifierWitness.honest_signAfterDigest key f dummy witnessCache _ _ result.1.signature hfull hreference


theorem registeredCanonicalCertificate_probability_le (key : SecretKey) (dummy : OtsReferenceWords)
    (reuse price : ENNReal) (required : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (cache : QueryCache HashSpec) (hashes signatures : Nat)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    Pr[RegisteredCanonicalCertificate key dummy required |
      (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] ≤
      price * hashes + Pr[fun result => result.2.2.stopped = true |
        (simulateQ (registeredCertificateImpl key reuse price required) computation).run
          (((cache, []), ∅), ⟨hashes, signatures, fun _ => false, false⟩)] := by
  let initial : RegisteredCertificateState := (((cache, []), ∅), ⟨hashes, signatures, fun _ => false, false⟩)
  let law := (simulateQ (registeredCertificateImpl key reuse price required) computation).run initial
  rw [← registeredCertificateImpl_forget key reuse price required computation initial, probEvent_map]
  have hcases : ∀ result ∈ support law,
      RegisteredCanonicalCertificate key dummy required (result.1, result.2.1) →
        (∃ input, result.2.2.bank input = true) ∨ result.2.2.stopped = true := by
    intro result hresult hcertificate
    by_cases hstopped : result.2.2.stopped = true
    · exact Or.inr hstopped
    have hproject : (result.1, result.2.1) ∈ support
        ((simulateQ (registeredTargetImpl key) computation).run initial.1) := by
      rw [← registeredCertificateImpl_forget key reuse price required computation initial, support_map]
      exact ⟨result, hresult, rfl⟩
    have hinvariant := RegisteredTargetInvariant.run key computation initial.1
      (RegisteredTargetInvariant.initial key cache hmessage) (result.1, result.2.1) hproject
    obtain ⟨input, hinput, hcovered⟩ := hcertificate.registered key dummy required _ hinvariant
    have hbank := registeredCertificate_run_covered key reuse price required computation initial
      (by intro _ input hinput; exact False.elim (Finset.notMem_empty input hinput)) result hresult
    exact Or.inl ⟨input, hbank (Bool.eq_false_iff.mpr hstopped) input hinput hcovered⟩
  exact (_root_.probEvent_mono hcases).trans ((probEvent_or_le law _ _).trans
    (add_le_add (registeredCertificate_probability_le key reuse price required computation cache hashes signatures) le_rfl))


theorem registeredCanonicalCertificate_le_message_excess (key : SecretKey) (dummy : OtsReferenceWords)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (cache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 127) (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q)
    (baseline : ENNReal) (hbaseline : baseline ≠ ⊤) :
    Pr[fun result => result.2.1.2.length ≤ signatureLimit ∧ RegisteredCanonicalCertificate key dummy required result |
      (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] ≤
      baseline * (∑' result, Pr[= result | (simulateQ (registeredSecurityLedgerImpl key required) computation).run
        (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)] * result.2.1.2.2.messages) +
      (q : ENNReal) * uniformWordAverage fixedProposalLength (fun word => terminalCertificatePrice required word - baseline) +
      proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q := by
  apply le_trans _ (registeredCertificate_probability_le_message_excess key required computation cache q (hq.trans (Nat.le_add_right _ _)) hfinite hmessage hbound baseline hbaseline)
  apply _root_.probEvent_mono
  rintro result hresult ⟨hvalid, hcertificate⟩
  exact ⟨hvalid, hcertificate.registered key dummy required result
    (RegisteredTargetInvariant.run key computation _ (RegisteredTargetInvariant.initial key cache hmessage) result hresult)⟩

end SphincsSecurity.Concrete
