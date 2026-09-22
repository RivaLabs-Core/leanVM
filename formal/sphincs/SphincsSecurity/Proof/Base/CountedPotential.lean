import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.QueryCap

namespace SphincsSecurity.QueryCap

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem probComp_nonempty {α : Type} (computation : ProbComp α) : (support computation).Nonempty := by
  by_contra h
  have := (probFailure_eq_one_iff_not_nonempty computation).mpr h
  simp at this

/-- A per-query potential bound also holds for budgets imposed only on supported executions. -/
theorem expected_potential_le {Index State α : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT State ProbComp))
    (invariant : State → Prop)
    (hpreserve : ∀ input state, invariant state → ∀ result ∈ support ((impl input).run state), invariant result.2)
    (selected : Index → Prop) [DecidablePred selected] (weight : State → ENNReal) (rate : ENNReal)
    (hstepBound : ∀ input state, invariant state →
      (∑' result, Pr[= result | (impl input).run state] * weight result.2) ≤
        weight state + rate * ((if selected input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp spec α) (state : State) (hinvariant : invariant state) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ impl (counted selected computation)).run state), result.1.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ impl computation).run state] * weight result.2) ≤ weight state + rate * q := by
  let charge : Index → Nat := fun input => if selected input then 1 else 0
  induction computation using OracleComp.inductionOn generalizing state q with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind input next ih =>
      have hsum : ∀ step ∈ support ((impl input).run state),
          ∀ tail ∈ support ((simulateQ (impl)
            (QueryCap.counted selected (next step.1))).run step.2),
            charge input + tail.1.2 ≤ q := by
        intro step hstep tail htail
        apply hbound ((tail.1.1, charge input + tail.1.2), tail.2)
        rw [QueryCap.counted_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        refine ⟨step, hstep, ?_⟩
        rw [bind_pure_comp, simulateQ_map, StateT.run_map, support_map]
        exact ⟨tail, htail, rfl⟩
      have hcost : charge input ≤ q := by
        obtain ⟨step, hstep⟩ := probComp_nonempty ((impl input).run state)
        obtain ⟨tail, htail⟩ := probComp_nonempty ((simulateQ (impl)
          (QueryCap.counted selected (next step.1))).run step.2)
        exact (Nat.le_add_right _ _).trans (hsum step hstep tail htail)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' step, Pr[= step | (impl input).run state] *
            (weight step.2 + rate * ((q - charge input : Nat) : ENNReal)) := by
          apply ENNReal.tsum_le_tsum
          intro step
          by_cases hstep : step ∈ support ((impl input).run state)
          · apply mul_le_mul' le_rfl
            apply ih step.1 step.2 (hpreserve input state hinvariant step hstep) (q - charge input)
            intro tail htail
            have := hsum step hstep tail htail
            omega
          · rw [probOutput_eq_zero_of_not_mem_support hstep, zero_mul, zero_mul]
        _ = (∑' step, Pr[= step | (impl input).run state] * weight step.2) +
            (∑' step, Pr[= step | (impl input).run state]) * (rate * ((q - charge input : Nat) : ENNReal)) := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ (weight state + rate * charge input) + rate * ((q - charge input : Nat) : ENNReal) :=
          add_le_add (hstepBound input state hinvariant)
            (mul_le_of_le_one_left' tsum_probOutput_le_one)
        _ = _ := by
          rw [add_assoc, ← mul_add, ← Nat.cast_add, Nat.add_sub_of_le hcost]

end SphincsSecurity.QueryCap
