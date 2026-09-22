import SphincsSecurity.Proof.Forced.InterfaceSmallBudget
import SphincsSecurity.Proof.Forced.InterfaceNearBound
import SphincsSecurity.Proof.Forced.InterfaceSmallArithmetic
import SphincsSecurity.Proof.Residual.InterfaceLargeBudget

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal

theorem security127_of_small_interface_budget (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ budgetSplit)
    (adversary : Security.Adversary) (hbound : Security.HasHashQueryBound adversary q) :
    Security.forgeAdvantage adversary ≤ (q : ENNReal) / 2 ^ 127 := by
  have hbudget : q ≤ 2 ^ 127 := hsmall.trans budgetSplit_le
  have hseed := Seeded.forgeAdvantage_le_randomizedReference adversary q (hbudget.trans_lt (by norm_num)) hbound
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hseed
  have hslots : (∑ slot ∈ Finset.range q, Pr[fun hit => hit = true |
      FtsGuessHash.forcedNearGame fixedReferenceDummy (Seeded.memoAdversary (Security.embed adversary)) slot]) ≤
      (q : ENNReal) * nearCertificateBound (q + 2 ^ 64) := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun slot _ =>
      FtsGuessHash.forcedNearGame_interface_le adversary q hbound hbudget fixedReferenceDummy slot).trans ?_
    rw [Finset.card_range, nsmul_eq_mul]
  have hn := forgeAdvantage_le_forcedNear_interface adversary q hbound hsmall fixedReferenceDummy
    (fun _ _ _ => fixedReferenceDummyWord_valid)
  exact (hseed.trans (add_le_add (hn.trans (add_le_add le_rfl (mul_le_mul' le_rfl hslots))) le_rfl)).trans
    (small_interface_bound_le_security127 q hq hsmall)

end SphincsSecurity.Concrete

namespace SphincsSecurity.Security
open ENNReal

theorem security127 : HasClassicalSecurityBits 127 := by
  intro q hq adversary hbound
  rw [Nat.cast_pow, Nat.cast_ofNat]
  by_cases hsmall : q ≤ Concrete.budgetSplit
  · exact Concrete.security127_of_small_interface_budget q hq hsmall adversary hbound
  · exact Concrete.security127_of_large_interface_budget q (by omega) adversary hbound

end SphincsSecurity.Security
