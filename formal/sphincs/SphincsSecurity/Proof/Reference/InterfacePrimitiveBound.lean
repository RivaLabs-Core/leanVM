import SphincsSecurity.Proof.Reference.ReferencePrimitiveBound
import SphincsSecurity.Proof.Reference.ReferenceInterfaceBudget
import SphincsSecurity.Proof.Ots.OtsInterfaceMarkerBounds

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs canonicalGraphLabels Finset.univ

theorem referenceGraphContextGame_primitive_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      primitivePrefixRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) +
      primitiveEncodingRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal)) +
      (Fintype.card Digest : ENNReal)⁻¹ * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.otherCalls dummy : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  let law := referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have he := referenceEncodingContextGame_match_le_encodingCost dummy adversary
  rw [← referenceGraphContextGame_encoding contactObserver _ _ dummy adversary, probEvent_map] at he
  have hs := referenceGraphContextGame_match_le_otherCost dummy adversary
  have ht := referenceContactGame_twoEdge_le_interface dummy original q hbound hsmall
  have hd := referenceContactGame_distinct_le_interface dummy original q hbound hsmall
  have hm := referenceContactGame_markerContact_le_interface dummy original q hbound hsmall
  dsimp only at ht hd hm
  rw [← referenceGraphContextGame_contact_event _ _ dummy (Seeded.memoAdversary (Security.embed original))] at ht hd hm
  have h := (probEvent_or_le law _ _).trans (add_le_add he
    ((probEvent_or_le law _ _).trans (add_le_add hs
      ((probEvent_or_le law _ _).trans (add_le_add ht
        ((probEvent_or_le law _ _).trans (add_le_add hd hm)))))))
  change Pr[GraphPrimitiveEvent dummy | law] ≤ _ at h
  refine h.trans_eq ?_
  simp only [primitivePrefixRate, primitiveEncodingRate, div_eq_mul_inv]
  ring

theorem referenceGraphContextGame_primitive_joint_budget_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest)
    (rate : ENNReal) (hp : primitivePrefixRate q ≤ rate) (he : primitiveEncodingRate q ≤ rate)
    (ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ rate) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      rate * (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.interfaceMessageCalls : ENNReal)) ≤ rate * q := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  let law := referenceRecordedGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have h := add_le_add (referenceGraphContextGame_primitive_le_interface dummy original q hbound hsmall)
    (le_refl (rate * ∑' result, Pr[= result | law] * (result.interfaceMessageCalls : ENNReal)))
  refine h.trans ?_
  calc
    _ ≤ rate * (∑' result, Pr[= result | law] * (result.prefixCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.encodingCalls : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.otherCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.interfaceMessageCalls : ENNReal)) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' hp le_rfl) (mul_le_mul' he le_rfl)) (mul_le_mul' ho le_rfl)) le_rfl
    _ = rate * ∑' result, Pr[= result | law] * ((result.prefixCalls dummy + result.encodingCalls + result.otherCalls dummy + result.interfaceMessageCalls : Nat) : ENNReal) := by
      simp only [Nat.cast_add, mul_add, ENNReal.tsum_add, add_assoc]
    _ ≤ rate * q := by
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑' result, Pr[= result | law] * (q : ENNReal) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support law
          · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (referenceRecordedGame_interface_allocation original q (hsmall.trans_le (by norm_num [digestBits])) hbound dummy result hr))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ ≤ q := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem referenceGraphContextGame_primitive_small_budget_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q ≤ budgetSplit) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      (primitiveCoefficient / Fintype.card Digest) *
        (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.interfaceMessageCalls : ENNReal)) ≤
        primitiveCoefficient * ((q : ENNReal) / Fintype.card Digest) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hq : q < Fintype.card Digest := hsmall.trans_lt (budgetSplit_le.trans_lt (by rw [hcard]; norm_num))
  have hr := primitive_rates_small q hsmall
  have ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ primitiveCoefficient / Fintype.card Digest := by
    rw [primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div, hcard]
  simpa only [div_eq_mul_inv, mul_right_comm, mul_assoc] using
    referenceGraphContextGame_primitive_joint_budget_interface dummy original q hbound hq _ hr.1 hr.2 ho

end SphincsSecurity.Concrete
