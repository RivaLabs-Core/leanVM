import SphincsSecurity.Proof.Forced.FtsGuessInterfaceNearSource
import SphincsSecurity.Proof.Reference.ReferenceCanonicalCertificate
import SphincsSecurity.Proof.Reference.InterfacePrimitiveBound

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphGameInputs canonicalEncodingInputs canonicalGraphInputs

private theorem combine_certificate (primitive certificate remaining messages rate baseline excess budget bound : ENNReal)
    (hcases : budget ≤ certificate + remaining + primitive)
    (hprimitive : primitive + rate * messages ≤ bound)
    (hcertificate : certificate ≤ baseline * messages + excess)
    (hprice : baseline ≤ rate) : budget ≤ bound + excess + remaining := by
  calc
    budget ≤ (baseline * messages + excess) + remaining + primitive :=
      hcases.trans (add_le_add (add_le_add hcertificate le_rfl) le_rfl)
    _ = (primitive + baseline * messages) + excess + remaining := by ac_rfl
    _ ≤ (primitive + rate * messages) + excess + remaining :=
      add_le_add (add_le_add (add_le_add le_rfl (mul_le_mul' hprice le_rfl)) le_rfl) le_rfl
    _ ≤ _ := add_le_add (add_le_add hprimitive le_rfl) le_rfl

theorem forgeAdvantage_le_remainingFts_interface (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q ≤ budgetSplit)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    forgeAdvantage scheme adversary ≤
      primitiveCoefficient * ((q : ENNReal) / 2 ^ 128) +
        ((q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q) +
        Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  have hcases := forgeAdvantage_le_canonical_cases dummy hdummy adversary
  have hcertificate := (referenceForgeryGame_canonicalFull_le dummy adversary).trans
    (originalCanonicalCertificate_full_le original q (hsmall.trans budgetSplit_le) hbound dummy)
  rw [registeredGameMessageExpectation_reference dummy adversary] at hcertificate
  have hprimitive := referenceGraphContextGame_primitive_small_budget_interface dummy original q hbound hsmall
  dsimp only at hprimitive
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at hprimitive
  have hprice : (2 ^ 128 : ENNReal)⁻¹ ≤ primitiveCoefficient / 2 ^ 128 := by
    rw [primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div]
  have hremaining : Pr[fun sample => sample.canonical dummy ∧ sample.remainingFts dummy |
      referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      Pr[ReferenceForgerySample.remainingFts dummy |
        referenceForgeryGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] :=
    _root_.probEvent_mono (fun _ _ h => h.2)
  exact combine_certificate _ _ _ _ _ _ _ _ _
    (hcases.trans (add_le_add (add_le_add le_rfl hremaining) le_rfl)) hprimitive hcertificate hprice

theorem referenceForgeryGame_remainingFts_interface (original : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound original q) (dummy : OtsReferenceWords) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      FtsGuessHash.pairRate q + ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q, Pr[fun hit => hit = true | FtsGuessHash.forcedNearGame dummy adversary slot] := by
  dsimp only
  refine (_root_.probEvent_mono'' (mx := referenceForgeryGame (canonicalGraphGameInputs (Seeded.memoAdversary (Security.embed original)))
    (canonicalEncodingInputs_subset_gameInputs _) dummy (Seeded.memoAdversary (Security.embed original)))
    (fun sample h => sample.remainingFts_cases dummy h)).trans ?_
  exact (probEvent_or_le _ _ _).trans (add_le_add
    (FtsGuessHash.referenceForgeryGame_two_guesses_interface original q hsmall hbound dummy)
    (FtsGuessHash.referenceForgeryGame_near_guess_le_forced_interface original q hsmall hbound dummy))

theorem forgeAdvantage_le_forcedNear_interface (original : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound original q) (hsmall : q ≤ budgetSplit)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    forgeAdvantage scheme adversary ≤
      primitiveCoefficient * ((q : ENNReal) / 2 ^ 128) +
        ((q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q) +
        ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
        ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
          ∑ slot ∈ Finset.range q, Pr[fun hit => hit = true | FtsGuessHash.forcedNearGame dummy adversary slot] := by
  have hq : q < 2 ^ 256 := (hsmall.trans budgetSplit_le).trans_lt (by norm_num)
  have h := (forgeAdvantage_le_remainingFts_interface original q hbound hsmall dummy hdummy).trans
    (add_le_add le_rfl (referenceForgeryGame_remainingFts_interface original q hq hbound dummy))
  have hp := FtsGuessHash.pairRate_le_normalized q
  exact h.trans (by rw [← add_assoc]; exact add_le_add (add_le_add le_rfl hp) le_rfl)

end SphincsSecurity.Concrete
