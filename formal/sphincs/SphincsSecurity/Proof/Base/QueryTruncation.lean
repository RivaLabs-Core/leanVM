import SphincsSecurity.Proof.Base.StatefulQueryCap

namespace SphincsSecurity.QueryCap
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]

noncomputable def truncate (computation : OracleComp spec α) (budget : Nat) (fallback : α) : OracleComp spec α :=
  (fun result => result.elim fallback Prod.fst) <$> run selected computation budget

theorem truncate_pure (value fallback : α) (budget : Nat) :
    truncate selected (pure value : OracleComp spec α) budget fallback = pure value := by
  simp only [truncate, run_pure, map_pure, Option.elim_some]

theorem truncate_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
    (budget : Nat) (fallback : α) :
    truncate selected (liftM (spec.query input) >>= next) budget fallback =
      if selected input then
        match budget with
        | 0 => pure fallback
        | remaining + 1 => liftM (spec.query input) >>= fun answer => truncate selected (next answer) remaining fallback
      else liftM (spec.query input) >>= fun answer => truncate selected (next answer) budget fallback := by
  rw [truncate, run_query_bind]
  split
  · cases budget <;> simp only [map_pure, Option.elim_none, map_bind, truncate]
  · simp only [map_bind, truncate]

theorem truncate_queryBound (computation : OracleComp spec α) (budget : Nat) (fallback : α) :
    (truncate selected computation budget fallback).IsQueryBoundP selected budget := by
  simpa only [truncate, isQueryBoundP_map_iff] using run_queryBound selected computation budget

theorem counted_truncate_bound (charge : ι → Prop) [DecidablePred charge] (impl : QueryImpl spec ProbComp)
    (computation : OracleComp spec α) (cap : Nat) (fallback : α) (budget : Nat)
    (hbound : ∀ result ∈ support (simulateQ impl (counted charge computation)), result.2 ≤ budget) :
    ∀ result ∈ support (simulateQ impl (counted charge (truncate selected computation cap fallback))), result.2 ≤ budget := by
  intro result hr
  rw [truncate, counted_map, simulateQ_map, support_map] at hr
  obtain ⟨before, hb, rfl⟩ := hr
  exact counted_run_bound selected charge impl computation cap budget hbound before hb

end SphincsSecurity.QueryCap
