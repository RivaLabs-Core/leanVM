import SphincsSecurity.Proof.Base.QueryCap
import SphincsSecurity.Proof.Base.Prelude

namespace SphincsSecurity.QueryCap
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index State Result : Type} {spec : OracleSpec Index}
  (selected : Index → Prop) [DecidablePred selected]

/-- Keep the final state only when the capped computation finishes. -/
def statefulFinish (budget : Nat) (result : (Result × Nat) × State) :
    Option ((Result × State) × Nat) :=
  if result.1.2 ≤ budget then some ((result.1.1, result.2), budget - result.1.2) else none

theorem stateful_run_eq_counted (impl : QueryImpl spec (StateT State PMF))
    (computation : OracleComp spec Result) (budget : Nat) (state : State) :
    ((simulateQ impl (run selected computation budget)).run state).map
      (fun result => result.1.map (fun value => ((value.1, result.2), value.2))) =
      ((simulateQ impl (counted selected computation)).run state).map (statefulFinish budget) := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure result =>
      simp [run_pure, counted_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_map, statefulFinish]
  | query_bind input next ih =>
      rw [run_query_bind, counted_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_pure, StateT.run_bind,
              PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
              Function.comp_def, statefulFinish, if_pos hs, Nat.add_comm 1, Nat.not_add_one_le_zero, if_false, PMF.bind_const, Option.map_none]
        | succ budget =>
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.map_bind]
            apply congrArg₂ PMF.bind rfl
            funext step
            rw [ih]
            simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
              PMF.map, PMF.pure_bind, Function.comp_def, statefulFinish, if_pos hs,
              Nat.add_comm 1, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.map_bind]
        apply congrArg₂ PMF.bind rfl
        funext step
        rw [ih]
        simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
          PMF.map, PMF.pure_bind, Function.comp_def, statefulFinish, Nat.zero_add]

private theorem probComp_support_nonempty {α : Type} (computation : ProbComp α) :
    (support computation).Nonempty := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact ⟨value, by simp⟩
  | query_bind input next ih =>
      obtain ⟨value, hv⟩ := ih default
      exact ⟨value, (mem_support_bind_iff _ _ _).mpr ⟨default, mem_support_query input default, hv⟩⟩

theorem counted_bind_first_bound {β : Type} (impl : QueryImpl spec ProbComp)
    (first : OracleComp spec Result) (next : Result → OracleComp spec β) (budget : Nat)
    (hbound : ∀ result ∈ support (simulateQ impl (counted selected (first >>= next))), result.2 ≤ budget) :
    ∀ result ∈ support (simulateQ impl (counted selected first)), result.2 ≤ budget := by
  intro result hr
  obtain ⟨tail, ht⟩ := probComp_support_nonempty (simulateQ impl (counted selected (next result.1)))
  have h : result.2 + tail.2 ≤ budget := by
    apply hbound (tail.1, result.2 + tail.2)
    simp only [counted_bind, simulateQ_bind, simulateQ_pure, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨result, hr, tail, ht, rfl⟩
  omega

theorem counted_query_bound {ι α : Type} {spec : OracleSpec ι}
    (selected : ι → Prop) [DecidablePred selected] (impl : QueryImpl spec ProbComp)
    (input : ι) (next : spec.Range input → OracleComp spec α) (q : Nat)
    (hbound : ∀ result ∈ support (simulateQ impl (counted selected (liftM (spec.query input) >>= next))), result.2 ≤ q)
    (answer : spec.Range input) (hanswer : answer ∈ support (impl input)) :
    (if selected input then 1 else 0) ≤ q ∧
      ∀ result ∈ support (simulateQ impl (counted selected (next answer))),
        result.2 ≤ q - (if selected input then 1 else 0) := by
  have hsum : ∀ result ∈ support (simulateQ impl (counted selected (next answer))),
      (if selected input then 1 else 0) + result.2 ≤ q := by
    intro result hresult
    apply hbound (result.1, (if selected input then 1 else 0) + result.2)
    simp only [counted_query_bind, bind_pure_comp, simulateQ_bind, simulateQ_spec_query,
      simulateQ_map, mem_support_bind_iff, support_map]
    exact ⟨answer, hanswer, result, hresult, rfl⟩
  obtain ⟨result, hresult⟩ := probComp_support_nonempty (simulateQ impl (counted selected (next answer)))
  exact ⟨by have := hsum result hresult; omega, fun result hresult => by have := hsum result hresult; omega⟩

theorem counted_run_bound (charge : Index → Prop) [DecidablePred charge]
    (impl : QueryImpl spec ProbComp) (computation : OracleComp spec Result) (cap q : Nat)
    (hbound : ∀ result ∈ support (simulateQ impl (counted charge computation)), result.2 ≤ q) :
    ∀ result ∈ support (simulateQ impl (counted charge (run selected computation cap))), result.2 ≤ q := by
  induction computation using OracleComp.inductionOn generalizing cap q with
  | pure value =>
      intro result hr
      simp only [run_pure, counted_pure, simulateQ_pure, mem_support_pure_iff] at hr
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [run_query_bind]
      have step (remaining : Nat) :
          ∀ result ∈ support (simulateQ impl (counted charge
            (liftM (spec.query input) >>= fun answer => run selected (next answer) remaining))), result.2 ≤ q := by
        intro result hr
        simp only [counted_query_bind, bind_pure_comp, simulateQ_bind, simulateQ_spec_query,
          simulateQ_map, mem_support_bind_iff, support_map] at hr
        obtain ⟨answer, ha, tail, ht, rfl⟩ := hr
        obtain ⟨hc, hn⟩ := counted_query_bound charge impl input next q hbound answer ha
        have hh := ih answer remaining _ hn tail ht
        dsimp only
        omega
      by_cases hs : selected input
      · rw [if_pos hs]
        cases cap with
        | zero =>
            intro result hr
            simp only [counted_pure, simulateQ_pure, mem_support_pure_iff] at hr
            subst result
            exact Nat.zero_le _
        | succ cap => exact step cap
      · rw [if_neg hs]
        exact step cap

end SphincsSecurity.QueryCap
