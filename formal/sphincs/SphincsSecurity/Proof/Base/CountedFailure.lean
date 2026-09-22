import SphincsSecurity.Proof.Base.CountedPotential

namespace SphincsSecurity.QueryCap

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def rememberFailure {Index State : Type} {spec : OracleSpec Index}
    (bad : State → Prop) (_input : Index) (_before : State) (_answer : spec.Range _input)
    (after : State) (failed : Bool) : Bool := failed || decide (bad after)

noncomputable def failureImpl {Index State : Type} {spec : OracleSpec Index}
    {m : Type → Type} [Monad m]
    (impl : QueryImpl spec (StateT State m)) (bad : State → Prop) :
    QueryImpl spec (StateT (State × Bool) m) :=
  QueryImpl.extendState impl (rememberFailure bad)

theorem failureImpl_forget {Index State α : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT State ProbComp)) (bad : State → Prop)
    (computation : OracleComp spec α) (state : State × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (failureImpl impl bad) computation).run state =
      (simulateQ impl computation).run state.1 :=
  extendState_run_proj_eq _ _ _ _ _

theorem failure_probability_le {Index State α : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT State ProbComp))
    (invariant : State → Prop)
    (hpreserve : ∀ input state, invariant state → ∀ result ∈ support ((impl input).run state), invariant result.2)
    (selected : Index → Prop) [DecidablePred selected] (weight : State → ENNReal) (rate : ENNReal)
    (hstep : ∀ input state, invariant state →
      (∑' result, Pr[= result | (impl input).run state] * weight result.2) ≤
        weight state + rate * ((if selected input then 1 else 0 : Nat) : ENNReal))
    (bad : State → Prop) (hbad : ∀ state, invariant state → bad state → 1 ≤ weight state)
    (computation : OracleComp spec α) (state : State) (hinvariant : invariant state) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ impl (counted selected computation)).run state), result.1.2 ≤ q) :
    Pr[fun result => result.2.2 = true | (simulateQ (failureImpl impl bad) computation).run (state, false)] ≤
      weight state + rate * q := by
  let potential : State × Bool → ENNReal := fun state => if state.2 then 1 else weight state.1
  have hpreserve' : ∀ input state, invariant state.1 →
      ∀ result ∈ support ((failureImpl impl bad input).run state), invariant result.2.1 := by
    intro input state hinvariant result hresult
    rw [failureImpl, QueryImpl.extendState_apply, bind_pure_comp, support_map] at hresult
    obtain ⟨step, hstep, rfl⟩ := hresult
    exact hpreserve input state.1 hinvariant step hstep
  have hstep' : ∀ input state, invariant state.1 →
      (∑' result, Pr[= result | (failureImpl impl bad input).run state] * potential result.2) ≤
        potential state + rate * ((if selected input then 1 else 0 : Nat) : ENNReal) := by
    intro input state hinvariant
    rw [failureImpl, QueryImpl.extendState_apply, bind_pure_comp, tsum_probOutput_map_mul]
    cases hfailed : state.2 with
    | true =>
        simp only [potential, rememberFailure, hfailed, Bool.true_or, if_true, mul_one]
        exact tsum_probOutput_le_one.trans le_self_add
    | false =>
        simp only [potential, rememberFailure, hfailed, Bool.false_or]
        apply le_trans ?_ (hstep input state.1 hinvariant)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support ((impl input).run state.1)
        · apply mul_le_mul' le_rfl
          by_cases hb : bad result.2
          · simpa only [hb, decide_true, if_true] using hbad result.2 (hpreserve input state.1 hinvariant result hr) hb
          · simp [hb]
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
  have hbound' : ∀ result ∈ support ((simulateQ (failureImpl impl bad) (counted selected computation)).run (state, false)),
      result.1.2 ≤ q := by
    intro result hresult
    apply hbound (result.1, result.2.1)
    rw [← failureImpl_forget impl bad (counted selected computation) (state, false), support_map]
    exact ⟨result, hresult, rfl⟩
  have hpotential := expected_potential_le (failureImpl impl bad) (fun state => invariant state.1)
    hpreserve' selected potential rate hstep' computation (state, false) hinvariant q hbound'
  refine le_trans ?_ hpotential
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hfailed
  simp only [potential, hfailed, if_true, le_refl]

end SphincsSecurity.QueryCap
