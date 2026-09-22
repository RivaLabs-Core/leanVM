import SphincsSecurity.Proof.Seeded.BudgetTransfer

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable (selected : OracleWorld.Domain → Prop) [DecidablePred selected]

def SelectedQueryBound {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ romImpl (QueryCap.counted selected computation)).run' cache), result.2 ≤ q

theorem selectedQueryBound_iff_run {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat) :
    SelectedQueryBound selected computation cache q ↔
      ∀ result ∈ support ((simulateQ romImpl (QueryCap.counted selected computation)).run cache), result.1.2 ≤ q := by
  simp only [SelectedQueryBound, StateT.run'_eq, support_map, Set.forall_mem_image]

theorem selectedQueryBound_bind {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : SelectedQueryBound selected (first >>= next) cache q)
    (result : (α × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (QueryCap.counted selected first)).run cache)) :
    result.1.2 ≤ q ∧ SelectedQueryBound selected (next result.1.1) result.2 (q - result.1.2) := by
  rw [selectedQueryBound_iff_run] at hbound ⊢
  simp only [QueryCap.counted_bind, simulateQ_bind, StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map] at hbound
  have hsum : ∀ tail ∈ support ((simulateQ romImpl (QueryCap.counted selected (next result.1.1))).run result.2),
      result.1.2 + tail.1.2 ≤ q := by
    intro tail htail
    apply hbound ((tail.1.1, result.1.2 + tail.1.2), tail.2)
    rw [mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [support_map]
    exact ⟨tail, htail, rfl⟩
  obtain ⟨tail, htail⟩ := probComp_support_nonempty ((simulateQ romImpl (QueryCap.counted selected (next result.1.1))).run result.2)
  exact ⟨by have := hsum tail htail; omega, fun tail htail => by have := hsum tail htail; omega⟩

theorem selectedQueryBound_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : SelectedQueryBound selected (liftM (OracleWorld.query input) >>= next) cache q)
    (result : OracleWorld.Range input × QueryCache HashSpec) (hr : result ∈ support ((romImpl input).run cache)) :
    (if selected input then 1 else 0) ≤ q ∧
      SelectedQueryBound selected (next result.1) result.2 (q - (if selected input then 1 else 0)) := by
  apply selectedQueryBound_bind selected _ next cache q hbound
    ((result.1, if selected input then 1 else 0), result.2)
  rw [← bind_pure (liftM (OracleWorld.query input)), QueryCap.counted_query_bind]
  simp only [QueryCap.counted_pure, map_pure, Nat.add_zero, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map]
  exact ⟨result, hr, rfl⟩

theorem selectedQueryBound_query_bind_of {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hcost : (if selected input then 1 else 0) ≤ q)
    (hnext : ∀ result ∈ support ((romImpl input).run cache),
      SelectedQueryBound selected (next result.1) result.2 (q - (if selected input then 1 else 0))) :
    SelectedQueryBound selected (liftM (OracleWorld.query input) >>= next) cache q := by
  intro result hresult
  rw [QueryCap.counted_query_bind, run'_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hresult⟩ := hresult
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, support_map] at hresult
  obtain ⟨tail, htail, rfl⟩ := hresult
  have htail' : tail.1 ∈ support ((simulateQ romImpl (QueryCap.counted selected (next step.1))).run' step.2) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨tail, htail, rfl⟩
  have h := hnext step hstep tail.1 htail'
  dsimp only
  omega

end SphincsSecurity.Seeded
