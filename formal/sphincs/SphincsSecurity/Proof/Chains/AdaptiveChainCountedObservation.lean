import SphincsSecurity.Proof.Chains.AdaptiveChainCountedCap
import SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge

namespace SphincsSecurity.Concrete.PartialChainEndpoint

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (budget : Nat)
  (hbound : ∀ result ∈ (realRun auxiliary
    (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support,
      result.2.1.2 ≤ budget)

include hbound

theorem realRun_cap_finished_of_counted
    (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) : ∃ finished, result.2.1 = some finished := by
  have hmap : Option.map Prod.fst result.2.1 ∈
      ((realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
        (fun result => Option.map Prod.fst result.2.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [realRun_cap_erased_of_counted auxiliary computation budget hbound, PMF.mem_support_map_iff] at hmap
  obtain ⟨source, _, hvalue⟩ := hmap
  cases hfinished : result.2.1 with
  | none => simp only [hfinished, Option.map_none, Option.some_ne_none] at hvalue
  | some finished => exact ⟨finished, rfl⟩

theorem idealRun_cap_finished_of_counted (hsmall : budget < Fintype.card State)
    (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) : ∃ finished, result.2.1 = some finished := by
  apply realRun_cap_finished_of_counted auxiliary computation budget hbound result
  exact idealRun_empty_support_subset auxiliary _ budget
    (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget) hsmall hresult

theorem realRun_cap_eq_counted_observed_of_counted :
    realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => (result.1, some (result.2.1.1, budget - result.2.1.2), result.2.2)) := by
  simp only [realRun, completeTables_empty, EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  rw [observedRun_cap_eq_counted (auxiliary (evaluate tables secret)) tables (computation (evaluate tables secret))
    (fun _ _ => none) budget (fixed_counted_le_of_counted auxiliary computation budget hbound tables secret), PMF.map_comp]
  simp only [Function.comp_def]

theorem realRun_cap_erased_observed_of_counted :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => (result.1, Option.map Prod.fst result.2.1, result.2.2)) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => (result.1, some result.2.1, result.2.2)) := by
  rw [realRun_cap_eq_counted_observed_of_counted auxiliary computation budget hbound, PMF.map_comp]
  have h := congrArg (PMF.map (fun result : State × (Result × (Fin n → State → Option State)) =>
    (result.1, some result.2.1, result.2.2))) (realRun_counted_forget auxiliary computation (fun _ _ => none))
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using h

theorem realRun_cap_contact_eq_of_counted :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin n → State → Option State))) =>
    Pr[fun result => Contact result.2.2 result.1 | law])
    (realRun_cap_erased_observed_of_counted auxiliary computation budget hbound)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem idealRun_counted_cap_spent_of_counted (hsmall : budget < Fintype.card State)
    (result : State × ((Option (Result × Nat) × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none)).support) :
    result.2.1.2 = QueryCap.spent budget result.2.1.1 := by
  have hforget : (result.1, result.2.1.1, result.2.2) ∈
      (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).support := by
    rw [← idealRun_counted_forget auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  obtain ⟨finished, hfinished⟩ := idealRun_cap_finished_of_counted auxiliary computation budget hbound hsmall _ hforget
  change result.2.1.1 = some finished at hfinished
  have hbalance := QueryCap.counted_run_balance IsPrefixQuery (computation result.1) budget result.2.1
    (idealRun_result_mem auxiliary _ (fun _ _ => none) result hresult)
  simp only [hfinished, Option.elim_some] at hbalance
  simp only [QueryCap.spent, hfinished, Option.elim_some]
  omega

theorem idealRun_cap_count_expectation_of_counted (hsmall : budget < Fintype.card State) :
    (∑' result, idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none) result *
          (result.2.1.2 : ENNReal)) =
      ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
        (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← idealRun_counted_forget auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none), expectation_map]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none)).support
  · rw [idealRun_counted_cap_spent_of_counted auxiliary computation budget hbound hsmall result hresult]
  · have hzero : idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none) result = 0 :=
      not_not.mp hresult
    simp only [hzero, zero_mul]

theorem realRun_cap_contact_le_of_counted (hsmall : budget < Fintype.card State) :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] ≤
        (2 / Fintype.card State) * ∑' result,
          idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
            (QueryCap.spent budget result.2.1 : ENNReal) := by
  have h := realRun_contact_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
  rwa [idealRun_cap_count_expectation_of_counted auxiliary computation budget hbound hsmall] at h

theorem realRun_contact_le_cap_cost_of_counted (hsmall : budget < Fintype.card State) :
    Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * ∑' result,
        idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
          (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_contact_eq_of_counted auxiliary computation budget hbound]
  exact realRun_cap_contact_le_of_counted auxiliary computation budget hbound hsmall

theorem realRun_cap_twoEdgeEvent_eq_of_counted :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin n → State → Option State))) =>
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | law])
    (realRun_cap_erased_observed_of_counted auxiliary computation budget hbound)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem realRun_twoEdgeEvent_le_cap_cost_of_counted (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  cases n with
  | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
  | succ n =>
    cases n with
    | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
    | succ n =>
      rw [← realRun_cap_twoEdgeEvent_eq_of_counted auxiliary computation budget hbound]
      have h := realRun_twoEdge_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
      rw [idealRun_cap_count_expectation_of_counted auxiliary computation budget hbound hsmall] at h
      exact h

end SphincsSecurity.Concrete.PartialChainEndpoint
