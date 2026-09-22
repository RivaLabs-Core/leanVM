import SphincsSecurity.Proof.Ots.OtsInterfaceFirstBounds
import SphincsSecurity.Proof.Ots.OtsInterfaceRestart
import SphincsSecurity.Proof.Reference.ContactInterfaceBudget
import SphincsSecurity.Proof.Ots.OtsDistinctContactBound
import SphincsSecurity.Proof.Ots.OtsContactMarkerBound

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec OtsEncodingMarker
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs OtsContactTrace.contacts Finset.univ

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hresult
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hresult

theorem referenceContactGame_newContact_le_interface (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (original : Security.Adversary) (budget : Nat) (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address | law] ≤
      ∑' result, Pr[= result | law] * (result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have h : ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      (∑' result : InstrumentedResult ContactResult, Pr[= result | prefixContactObservedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (if result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address then 1 else 0)) ≤
      ∑' result : InstrumentedResult ContactResult, Pr[= result | prefixContactObservedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : ENNReal) := by
    unfold prefixContactObservedGame prefixInstrumentedObservedGame
    apply QueryCap.scaled_expectation_bind_le
    intro parameter hparameter
    apply QueryCap.scaled_expectation_bind_le
    intro ftsSecret _
    apply QueryCap.scaled_expectation_bind_le
    intro selections hselections
    apply QueryCap.scaled_expectation_bind_le
    intro other _
    apply QueryCap.scaled_expectation_bind_le
    intro auxiliary hauxiliary
    let words := referenceFamilyWords selections dummy
    let segment := OtsPrefix.atAddress parameter words address
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
    have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
        (fun endpoint => QueryCap.counted PartialChainEndpoint.IsPrefixQuery
          (segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary)) (fun _ _ => none)).support,
        result.2.1.2 ≤ budget :=
      prefixObservedRun_interface_budget parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
        address dummy original selections (pmf_mem_of_evalDist _ selections hselections)
        budget (hsmall.trans_le (by norm_num [digestBits])) hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
    have hseed := contactSeed_newContact_le_of_counted parameter words address inputs hencoding hgraph auxiliary other.val ftsSecret adversary budget hreal hsmall
    simp only [← PMF.monad_map_eq_map, evalDist_map, tsum_probOutput_bind_mul, tsum_probOutput_map_mul, tsum_probOutput_pure_mul]
    simpa only [PMF.evalDist_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero, mul_assoc] using hseed
  simpa only [prefixContactObservedGame_original, probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero] using h

theorem referenceContactGame_restart_allocation_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < 2 ^ 256) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    (∑ address : OtsPrefix.ChainAddress, ∑' result : InstrumentedResult ContactResult,
      Pr[= result | law] * (result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : ENNReal)) ≤
        ((2 * budget : Nat) : ENNReal) * Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) | law] := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  calc
    _ = ∑' result : InstrumentedResult ContactResult, Pr[= result | law] *
        ((∑ address : OtsPrefix.ChainAddress, result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : Nat) : ENNReal) := by
      rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
      simp only [tsum_fintype, Nat.cast_sum, Finset.mul_sum, law, adversary]
    _ ≤ ∑' result : InstrumentedResult ContactResult, Pr[= result | law] *
        if result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) then ((2 * budget : Nat) : ENNReal) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support law
      · apply mul_le_mul' le_rfl
        have hcost := referenceContactGame_interface_budget original budget hsmall hbound dummy result hr
        have hn := ContactResult.restartCharge_sum_le result.1 (referenceFamilyWords result.2.1 dummy) result.2.2 budget hcost
        by_cases hm : result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy)
        · rw [if_pos hm] at hn ⊢
          exact_mod_cast hn
        · rw [if_neg hm] at hn ⊢
          exact_mod_cast hn
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      by_cases hm : result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy)
      · simp only [if_pos hm, mul_comm, law, adversary]
      · simp only [if_neg hm, mul_zero]

theorem referenceContactGame_distinct_restart_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) | law] ≤
      ((2 * budget : Nat) : ENNReal) * Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) | law] := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => referenceContactGame_newContact_le_interface address dummy original budget hbound hsmall
  rw [← Finset.mul_sum] at hsum
  exact (mul_le_mul' le_rfl (referenceContactGame_twoContacts_le_sum _ _ dummy adversary)).trans
    (hsum.trans (referenceContactGame_restart_allocation_interface dummy original budget hbound (hsmall.trans_le (by norm_num [digestBits]))))

theorem referenceContactGame_distinct_cost_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    (1 - (q : ENNReal) / Fintype.card Digest)^2 * (Fintype.card Digest : ENNReal) *
      Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (4 * ((q : ENNReal) / Fintype.card Digest)) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hrestart := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest))
    (referenceContactGame_distinct_restart_le_interface dummy original q hbound hsmall)
  have hfirst := mul_le_mul' (le_refl (2 * (q : ENNReal)))
    (referenceContactGame_marked_cost_le_interface dummy original q hbound hsmall)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hrestart
  rw [mul_left_comm (1 - (q : ENNReal) / Fintype.card Digest) (2 * (q : ENNReal))] at hrestart
  have h := hrestart.trans hfirst
  convert h using 1 <;> first | rfl | (simp only [div_eq_mul_inv]; ring)

theorem referenceContactGame_distinct_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[fun result => result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (4 * ((q : ENNReal) / Fintype.card Digest) *
        (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal))) /
        ((1 - (q : ENNReal) / Fintype.card Digest)^2 * (Fintype.card Digest : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (q : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hpositive)) hcard)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_distinct_cost_le_interface dummy original q hbound hsmall

theorem referenceContactGame_contactMarker_le_contacts_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < 2 ^ 256) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[fun result => ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
      (result.2.2.before * result.2.2.after) | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((OtsCode.unitNeighborBound : ENNReal) * ((budget : ENNReal) / Fintype.card Digest)) * ∑' result,
        Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hcost : (∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
        (contactMarkerCost result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier 1 (result.2.2.before * result.2.2.after) : ENNReal)) ≤
      (budget : ENNReal) * ∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal) := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ support (referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    · have hl := referenceContactGame_interface_budget original budget hsmall hbound dummy result hr
      have hc := (contactMarkerCost_le result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier 1
        (result.2.2.before * result.2.2.after)).trans (Nat.mul_le_mul_right _ hl)
      simp only [one_mul] at hc
      rw [mul_left_comm (budget : ENNReal)]
      apply mul_le_mul' le_rfl
      exact_mod_cast hc
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, mul_zero]
  refine (referenceContactGame_contactMarker_le_cost _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary).trans
    ((mul_le_mul' le_rfl hcost).trans_eq ?_)
  simp only [div_eq_mul_inv]
  ring

theorem referenceContactGame_contactMarker_shared_bound_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => ContactBeforeMarker result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
        (result.2.2.before * result.2.2.after) | referenceContactGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((2 * (OtsCode.unitNeighborBound : ENNReal)) * ((budget : ENNReal) / Fintype.card Digest)) * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.prefixCalls dummy : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hraw := mul_le_mul' (le_refl (1 - (budget : ENNReal) / Fintype.card Digest))
    (referenceContactGame_contactMarker_le_contacts_interface dummy original budget hbound (hsmall.trans_le (by norm_num [digestBits])))
  rw [mul_left_comm] at hraw
  have hc := hraw.trans (mul_le_mul' le_rfl (referenceContactGame_contacts_cost_le_interface dummy original budget hbound hsmall))
  have hn : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := mul_le_mul' (le_refl (Fintype.card Digest : ENNReal)) hc
  have hcancel : (Fintype.card Digest : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel hn (by finiteness)
  rw [mul_left_comm (Fintype.card Digest : ENNReal), ← mul_assoc] at h
  refine h.trans_eq ?_
  simp only [div_eq_mul_inv]
  calc
    _ = (2 * (OtsCode.unitNeighborBound : ENNReal)) * ((budget : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) *
        (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) *
        ((Fintype.card Digest : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by ring
    _ = _ := by rw [hcancel, mul_one]

end SphincsSecurity.Concrete
