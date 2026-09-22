import SphincsSecurity.Proof.Chains.AdaptiveChainCapCost

namespace SphincsSecurity.Concrete.PartialChainEndpoint

open OracleComp OracleSpec ENNReal
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

theorem fixed_counted_le_of_counted (tables : Fin n → State → State) (secret : State) (result : Result × Nat)
    (hresult : result ∈ (simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables)
      (QueryCap.counted IsPrefixQuery (computation (evaluate tables secret)))).support) : result.2 ≤ budget := by
  have hsource := realRun_empty_result_mem auxiliary
    (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) tables secret result hresult
  rw [PMF.mem_support_map_iff] at hsource
  obtain ⟨source, hsource, hvalue⟩ := hsource
  simpa only [hvalue] using hbound source hsource

theorem realRun_cap_erased_of_counted :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map Prod.fst result.2.1) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map Prod.fst ∘ (fun result => result.2.1)) =
    (realRun auxiliary computation (fun _ _ => none)).map (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_erased IsPrefixQuery _ _ budget
    (fixed_counted_le_of_counted auxiliary computation budget hbound tables secret)

theorem realRun_cap_recover_count_of_counted :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map (fun finished => (finished.1, budget - finished.2)) result.2.1) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map (fun finished => (finished.1, budget - finished.2)) ∘ (fun result => result.2.1)) =
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
      (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_recover_count IsPrefixQuery _ _ budget
    (fixed_counted_le_of_counted auxiliary computation budget hbound tables secret)

theorem idealRun_cap_spent_lower_of_counted :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
          (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal)) ≤
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  apply (realRun_empty_cost_lower auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
    (fun result => (QueryCap.spent budget result.2.1 : ENNReal))).trans_eq
  have h := congrArg (fun law : PMF (Option (Result × Nat)) =>
    ∑' result, law result * result.elim 0 (fun finished => (finished.2 : ENNReal)))
    (realRun_cap_recover_count_of_counted auxiliary computation budget hbound)
  simp only [expectation_map, Option.elim_map, Option.elim_some, Function.comp_def] at h
  refine Eq.trans ?_ h
  apply tsum_congr
  intro result
  congr 1
  cases result.2.1 <;> simp only [QueryCap.spent, Option.elim_none, Option.elim_some, Nat.cast_zero]

end SphincsSecurity.Concrete.PartialChainEndpoint
