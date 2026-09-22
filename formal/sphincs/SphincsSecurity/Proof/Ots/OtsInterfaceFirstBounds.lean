import SphincsSecurity.Proof.Ots.OtsPrefixInterfaceProbability
import SphincsSecurity.Proof.Ots.OtsTwoEdgeProbability
import SphincsSecurity.Proof.Ots.OtsContactFirstProbability

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs OtsContactTrace.contacts Finset.univ

theorem referenceContactGame_twoEdge_sum_cost_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    (1 - (q : ENNReal) / Fintype.card Digest) *
      (∑ address : OtsPrefix.ChainAddress, Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary]) ≤
      prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  simp only [referenceContactGame_twoEdge_eq _ _ (canonicalGraphInputs_subset_gameInputs (Seeded.memoAdversary (Security.embed original)))]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixTwoEdgeGame_le_interface address dummy original q hbound hsmall
  rw [← Finset.mul_sum] at hsum
  have hlower := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixIdealCostGame_lower_interface address dummy original q hbound (hsmall.trans_le (by norm_num [digestBits]))
  rw [← Finset.mul_sum] at hlower
  simp only [prefixCountedObservedGame_original, tsum_probOutput_map_mul, ReferenceRecordedResult.prefixCounted] at hlower
  conv at hlower =>
    rhs
    rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
    simp only [tsum_fintype, ← Finset.mul_sum, ← Nat.cast_sum]
  have hscaled := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest)) hsum
  rw [mul_left_comm] at hscaled
  exact hscaled.trans (mul_le_mul' le_rfl hlower)

theorem referenceContactGame_twoEdge_cost_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    (1 - (q : ENNReal) / Fintype.card Digest) *
      Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  exact
  (mul_le_mul' le_rfl (referenceContactGame_twoEdge_le_sum _ _ dummy adversary)).trans
    (referenceContactGame_twoEdge_sum_cost_le_interface dummy original q hbound hsmall)

theorem referenceContactGame_twoEdge_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal))) /
        (1 - (q : ENNReal) / Fintype.card Digest) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (q : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hpositive)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_twoEdge_cost_le_interface dummy original q hbound hsmall

theorem referenceContactGame_contacts_cost_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    (1 - (q : ENNReal) / Fintype.card Digest) *
      (∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal)) ≤
      (2 / Fintype.card Digest) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  rw [← referenceContactGame_sum_contact_probability _ _ (canonicalGraphInputs_subset_gameInputs adversary)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixContactGame_le_interface address dummy original q hbound hsmall
  rw [← Finset.mul_sum] at hsum
  have hlower := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixIdealCostGame_lower_interface address dummy original q hbound (hsmall.trans_le (by norm_num [digestBits]))
  rw [← Finset.mul_sum] at hlower
  simp only [prefixCountedObservedGame_original, tsum_probOutput_map_mul, ReferenceRecordedResult.prefixCounted] at hlower
  conv at hlower =>
    rhs
    rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
    simp only [tsum_fintype, ← Finset.mul_sum, ← Nat.cast_sum]
  have hscaled := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest)) hsum
  rw [mul_left_comm] at hscaled
  exact hscaled.trans (mul_le_mul' le_rfl hlower)

theorem referenceContactGame_marked_cost_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    (1 - (q : ENNReal) / Fintype.card Digest) *
      Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (2 / Fintype.card Digest) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have h := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest))
    (referenceContactGame_marked_le_sum _ (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary)
  rw [referenceContactGame_sum_contact_probability] at h
  exact h.trans (referenceContactGame_contacts_cost_le_interface dummy original q hbound hsmall)

end SphincsSecurity.Concrete
