import SphincsSecurity.Proof.Residual.CappedExceptionBound
import SphincsSecurity.Proof.Residual.Security127LargeBudget
import SphincsSecurity.Proof.Deterministic.InterfaceReference

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
set_option maxRecDepth 4096

private theorem honest_allowance_and_seed_le_reserve (q : Nat) (hq : budgetSplit ≤ q) :
    (2 ^ 64 : ENNReal) * fullCertificateExcessRate + (2 ^ 64 : ENNReal) / 2 ^ 128 +
      (2 ^ 64 : ENNReal) * certificateCacheExceptionRate + (q : ENNReal) / 2 ^ 256 ≤ (q : ENNReal) / 2 ^ 160 := by
  apply le_trans (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl certificateCacheExceptionRate_le)) le_rfl)
  have hc : (2 ^ 64 : ENNReal) * fullCertificateExcessRate + (2 ^ 64 : ENNReal) / 2 ^ 128 +
      (2 ^ 64 : ENNReal) / 2 ^ 169 ≤ (budgetSplit : ENNReal) / 2 ^ 161 := by
    rw [fullCertificateExcessRate_def, budgetSplit_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    norm_num
  have hm : (budgetSplit : ENNReal) / 2 ^ 161 ≤ (q : ENNReal) / 2 ^ 161 :=
    ENNReal.div_le_div_right (by exact_mod_cast hq) _
  have hs : (q : ENNReal) / 2 ^ 256 ≤ (q : ENNReal) / 2 ^ 161 :=
    ENNReal.div_le_div_left (by norm_num) _
  calc
    _ ≤ (q : ENNReal) / 2 ^ 161 + (q : ENNReal) / 2 ^ 161 :=
      add_le_add (by simpa only [div_eq_mul_inv] using hc.trans hm) hs
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
      ring

theorem security127_of_large_interface_budget (q : Nat) (hlarge : budgetSplit ≤ q)
    (adversary : Security.Adversary) (hcost : Security.HasHashQueryBound adversary q) :
    Security.forgeAdvantage adversary ≤ (q : ENNReal) / 2 ^ 127 := by
  by_cases hsmall : q ≤ 2 ^ 127
  · have hs : q < 2 ^ 256 := hsmall.trans_lt (by norm_num)
    have hseed := Seeded.forgeAdvantage_le_randomizedReference adversary q hs hcost
    have hnative := RetainedResidual.forgeAdvantage_le_capped_native_bound fixedReferenceDummy
      (fun _ _ _ => fixedReferenceDummyWord_valid) adversary q hcost hsmall
    apply (hseed.trans (add_le_add hnative le_rfl)).trans
    have ha := honest_allowance_and_seed_le_reserve q hlarge
    have hc := native_bound_with_reserve_le_security127 q hlarge hsmall
    apply le_trans ?_ hc
    calc
      _ = (ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2) +
          q * fullCertificateExcessRate + (q * certificateCacheExceptionRate + proposalPrefixExceptionBound)) +
          (2 ^ 64 * fullCertificateExcessRate + 2 ^ 64 / 2 ^ 128 + 2 ^ 64 * certificateCacheExceptionRate + q / 2 ^ 256) := by
        simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        ring
      _ ≤ _ := add_le_add le_rfl ha
  · apply (show Security.forgeAdvantage adversary ≤ 1 from probEvent_le_one).trans
    calc
      (1 : ENNReal) = (2 ^ 127 : ENNReal) / 2 ^ 127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 2 ^ 127 ≤ q by omega)) _

end SphincsSecurity.Concrete
