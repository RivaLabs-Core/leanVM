import SphincsSecurity.Proof.Ots.OtsInterfaceTraceProbability
import SphincsSecurity.Proof.Ots.OtsInterfaceContactBounds
import SphincsSecurity.Proof.Ots.OtsMarkerContactProbability

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ OtsContactTrace.contacts

theorem markerCheckpointGame_contact_le_marker_interface (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (original : Security.Adversary) (budget : Nat) (hbound : Security.HasHashQueryBound original budget)
    (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address |
        markerCheckpointGame address (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (2 * budget : Nat) * Pr[fun result => OtsEncodingMarker.Seen result.1 (referenceFamilyWords result.2.1 dummy) address
        (result.2.2.before * result.2.2.after) | referenceContactGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have h := referenceCheckpointGame_newContact_le_mark_interface (OtsEncodingMarker.stopAt address) address dummy original budget hbound hsmall
  refine h.trans (mul_le_mul' le_rfl ?_)
  rw [← markerCheckpointGame_marker_probability]
  exact _root_.probEvent_mono (fun result _ hm => (OtsEncodingMarker.seen_mul _ _ _ _ _).mpr (Or.inl hm))


theorem markerCheckpointGame_contact_shared_bound_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      (∑ address : OtsPrefix.ChainAddress,
        Pr[fun result => result.2.2.ContactAfterStop (OtsEncodingMarker.stopAt address) result.1 (referenceFamilyWords result.2.1 dummy) address |
          markerCheckpointGame address (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary]) ≤
      ((2 * (OtsCode.neighborBound : ENNReal)) * ((budget : ENNReal) / Fintype.card Digest)) * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.encodingCalls : ENNReal) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    (fun address _ => markerCheckpointGame_contact_le_marker_interface address dummy original budget hbound hsmall)
  rw [← Finset.mul_sum, ← Finset.mul_sum, referenceContactGame_sum_marker_probability] at hsum
  refine hsum.trans ((mul_le_mul' le_rfl (referenceContactGame_markers_le_encodingCost dummy adversary)).trans_eq ?_)
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring


theorem referenceContactGame_markerContact_shared_bound_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((2 * (OtsCode.unitNeighborBound : ENNReal)) * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.prefixCalls dummy : ENNReal)) +
      ((2 * (OtsCode.neighborBound : ENNReal)) * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.encodingCalls : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have h := mul_le_mul' (le_refl ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)))
    (referenceContactGame_markerContact_partition (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
  rw [mul_add] at h
  exact h.trans (add_le_add (referenceContactGame_contactMarker_shared_bound_interface dummy original budget hbound hsmall)
    (markerCheckpointGame_contact_shared_bound_interface dummy original budget hbound hsmall))

theorem referenceContactGame_markerContact_le_interface (dummy : OtsReferenceWords) (original : Security.Adversary) (budget : Nat)
    (hbound : Security.HasHashQueryBound original budget) (hsmall : budget < Fintype.card Digest) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[fun result => result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (((2 * (OtsCode.unitNeighborBound : ENNReal)) * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.prefixCalls dummy : ENNReal)) +
       ((2 * (OtsCode.neighborBound : ENNReal)) * ((budget : ENNReal) / Fintype.card Digest)) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          (result.encodingCalls : ENNReal))) /
        ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (budget : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (ne_of_gt hpositive) hcard)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_markerContact_shared_bound_interface dummy original budget hbound hsmall


end SphincsSecurity.Concrete
