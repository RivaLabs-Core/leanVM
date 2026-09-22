import SphincsSecurity.Proof.Forced.Security127SmallBudgetArithmetic

namespace SphincsSecurity.Concrete
open ENNReal
set_option exponentiation.threshold 1024

theorem nearCertificateBound_honest_allowance (q : Nat) :
    nearCertificateBound (q + 2 ^ 64) ≤ nearCertificateBound q + (2 ^ 48 : ENNReal)⁻¹ := by
  have hc : (Fintype.card FtsTree : ENNReal) *
      (((2 ^ 64 : Nat) : ENNReal) * nearCertificatePrice + ((2 ^ 64 : Nat) : ENNReal) * certificateCacheExceptionRate) ≤
      (2 ^ 48 : ENNReal)⁻¹ := by
    refine (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl certificateCacheExceptionRate_le))).trans ?_
    rw [nearCertificatePrice_def, show Fintype.card FtsTree = 14 from Fintype.card_fin _]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    norm_num
  calc
    nearCertificateBound (q + 2 ^ 64) = nearCertificateBound q + (Fintype.card FtsTree : ENNReal) *
        (((2 ^ 64 : Nat) : ENNReal) * nearCertificatePrice + ((2 ^ 64 : Nat) : ENNReal) * certificateCacheExceptionRate) := by
      unfold nearCertificateBound
      rw [Nat.cast_add]
      ring
    _ ≤ _ := add_le_add le_rfl hc

private theorem interface_extra_le_reserve (q : Nat) (hsmall : q ≤ 2 ^ 127) :
    4 * certificateCacheExceptionRate * q + ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
      ((q : ENNReal) * (2 ^ 48 : ENNReal)⁻¹) + (q : ENNReal) / 2 ^ 256 ≤ (q : ENNReal) / 2 ^ 160 := by
  have hinv : ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ ≤ (2 ^ 127 : ENNReal)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast (show 2 ^ 127 ≤ 2 ^ 128 - q by omega)
  refine (add_le_add (add_le_add (mul_le_mul' (mul_le_mul' le_rfl certificateCacheExceptionRate_le) le_rfl)
    (mul_le_mul' hinv le_rfl)) le_rfl).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  norm_num
  nlinarith

theorem small_interface_bound_le_security127 (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ budgetSplit) :
    primitiveCoefficient * ((q : ENNReal) / 2 ^ 128) +
      ((q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q) +
      ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ((q : ENNReal) * nearCertificateBound (q + 2 ^ 64)) +
      (q : ENNReal) / 2 ^ 256 ≤ (q : ENNReal) / 2 ^ 127 := by
  have he := interface_extra_le_reserve q (hsmall.trans budgetSplit_le)
  refine (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl
    (mul_le_mul' le_rfl (nearCertificateBound_honest_allowance q)))) le_rfl).trans ?_
  calc
    _ = (primitiveCoefficient * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * fullCertificateExcessRate +
        proposalPrefixExceptionBound + ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
        ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ((q : ENNReal) * nearCertificateBound q)) +
        (4 * certificateCacheExceptionRate * q + ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
          ((q : ENNReal) * (2 ^ 48 : ENNReal)⁻¹) + (q : ENNReal) / 2 ^ 256) := by ring
    _ ≤ _ := (add_le_add le_rfl he).trans (small_bound_with_reserve_le_security127 q hq hsmall)

end SphincsSecurity.Concrete
