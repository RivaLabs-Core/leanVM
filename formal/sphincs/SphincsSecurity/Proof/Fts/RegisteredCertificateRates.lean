import SphincsSecurity.Proof.Fts.RegisteredMessageAllocation
import SphincsSecurity.Proof.Fts.UnitCertificateCoverage
import SphincsSecurity.Proof.Fts.NearCertificateBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def registeredMessageQueryExpectation {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' result, Pr[= result | (simulateQ (registeredTargetImpl key)
    (QueryCap.counted (IsMessageQuery key.parameter) computation)).run ((cache, []), ∅)] * result.1.2

def RegisteredCertificateEvent {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (result : α × RegisteredTargetState) : Prop :=
  result.2.1.2.length ≤ signatureLimit ∧ ∃ input ∈ result.2.2, TargetCertificateAt key required result.2.1 input

theorem registeredFullCertificate_probability_le {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q) :
    Pr[RegisteredCertificateEvent key Finset.univ |
      (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] ≤
      (2 ^ 128 : ENNReal)⁻¹ * registeredMessageQueryExpectation key computation cache +
      (q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q := by
  apply (registeredCertificate_probability_le_message_excess key Finset.univ computation cache q hq hfinite hmessage hbound
    (2 ^ 128 : ENNReal)⁻¹ (by finiteness)).trans
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul' le_rfl (expected_registeredMessages_le_counted key Finset.univ _ computation cache q))
    (mul_le_mul' le_rfl uniformWordAverage_full_price_excess_le)) le_rfl) le_rfl

theorem registeredNearCertificate_probability_le {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (hdegree : required.card + 1 = Fintype.card FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q) :
    Pr[RegisteredCertificateEvent key required |
      (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] ≤
      (q : ENNReal) * nearCertificatePrice + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q := by
  have h := registeredCertificate_probability_le_message_excess key required computation cache q hq hfinite hmessage hbound
    0 ENNReal.zero_ne_top
  simp only [zero_mul, zero_add, tsub_zero] at h
  exact h.trans (add_le_add (add_le_add (mul_le_mul' le_rfl (uniformWordAverage_nearPrice required hdegree)) le_rfl) le_rfl)

end SphincsSecurity.Concrete
