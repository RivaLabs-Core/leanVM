import SphincsSecurity.Proof.Base.QueryTruncation
import SphincsSecurity.Proof.Residual.SigningCap
import SphincsSecurity.Proof.Forced.FtsGuessNearAssembly

namespace SphincsSecurity.Concrete.FtsGuessHash
open OracleComp OracleSpec ENNReal OtsContactTrace
open RetainedResidual (IsSigningRequest)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)

theorem cached_adversary_truncate_weight (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (cap : Nat) (fallback : Forgery) (state : CachedState) (weight : AdversaryTrace × CachedState → ENNReal)
    (hzero : ∀ result, cap < result.1.1.1.2.length → weight result = 0) :
    (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (adversaryRun parameter labels computation) state] * weight result) ≤
    ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (adversaryRun parameter labels (QueryCap.truncate IsSigningRequest computation cap fallback)) state] * weight result := by
  induction computation using OracleComp.inductionOn generalizing cap state weight with
  | pure value => rw [QueryCap.truncate_pure]
  | query_bind input next ih =>
      rw [QueryCap.truncate_query_bind]
      have hlen (step : AdversaryStep input) (tail : AdversaryTrace) :
          (combineStep input step tail).1.1.2.length = (if IsSigningRequest input then 1 else 0) + tail.1.1.2.length := by
        cases input <;> simp only [combineStep, signingLogFragment, List.nil_append, List.length_append,
          List.length_singleton, IsSigningRequest, if_false, if_true, Nat.zero_add]
      have step (remaining : Nat) (hc : cap = (if IsSigningRequest input then 1 else 0) + remaining) :
          (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
            (adversaryRun parameter labels (liftM ((OracleWorld + SigningSpec).query input) >>= next)) state] * weight result) ≤
          ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
            (adversaryRun parameter labels (liftM ((OracleWorld + SigningSpec).query input) >>=
              fun answer => QueryCap.truncate IsSigningRequest (next answer) remaining fallback)) state] * weight result := by
        rw [cachedForcedRun_adversaryRun_query_bind, cachedForcedRun_adversaryRun_query_bind,
          tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
        apply ENNReal.tsum_le_tsum
        intro first
        rw [tsum_probOutput_map_mul, tsum_probOutput_map_mul]
        apply mul_le_mul' le_rfl
        apply ih first.1.1.1 remaining first.2 (fun tail => weight (combineStep input first.1 tail.1, tail.2))
        intro tail ht
        apply hzero
        dsimp only
        rw [hlen, hc]
        omega
      by_cases hs : IsSigningRequest input
      · rw [if_pos hs]
        cases cap with
        | zero =>
          have hz : (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
              (adversaryRun parameter labels (liftM ((OracleWorld + SigningSpec).query input) >>= next)) state] * weight result) = 0 := by
            rw [cachedForcedRun_adversaryRun_query_bind, tsum_probOutput_bind_mul]
            apply ENNReal.tsum_eq_zero.mpr
            intro first
            rw [tsum_probOutput_map_mul]
            have ht : (∑' tail, Pr[= tail | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
                (adversaryRun parameter labels (next first.1.1.1)) first.2] * weight (combineStep input first.1 tail.1, tail.2)) = 0 := by
              apply ENNReal.tsum_eq_zero.mpr
              intro tail
              rw [hzero _ (by dsimp only; rw [hlen, if_pos hs]; omega), mul_zero]
            rw [ht, mul_zero]
          rw [hz]
          exact zero_le
        | succ cap => exact step cap (by rw [if_pos hs]; omega)
      · rw [if_neg hs]
        exact step cap (by rw [if_neg hs, Nat.zero_add])

noncomputable def signingTruncatedAdversary (adversary : Adversary) : Adversary :=
  ⟨fun publicKey => QueryCap.truncate IsSigningRequest (adversary.main publicKey) signatureLimit zeroForgery⟩

theorem nearLaw_signing_truncation (adversary : Adversary) :
    Pr[fun result => completedNearCertificate parameter root result.1 |
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary] ≤
    Pr[fun result => completedNearCertificate parameter root result.1 |
      nearLaw parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingTruncatedAdversary adversary)] := by
  simp only [nearLaw, completedRun, cachedForcedRun_bind, cachedForcedRun_pure,
    probEvent_bind_eq_tsum, probEvent_pure]
  apply cached_adversary_truncate_weight parameter root otsSecret labels inputs hencoding selections rows dummy slot
    (adversary.main ⟨root, parameter⟩) signatureLimit zeroForgery
  intro before hlog
  apply ENNReal.tsum_eq_zero.mpr
  intro checked
  have hfalse : ¬ completedNearCertificate parameter root (before.1, checked.1) := by
    intro h
    exact Nat.not_le_of_gt hlog h.1
  simp only [if_neg hfalse, mul_zero]

end SphincsSecurity.Concrete.FtsGuessHash
