import SphincsSecurity.Proof.Adversary.Accounting
import SphincsSecurity.Proof.Seeded.QueryBoundExtras
open OracleComp OracleSpec SphincsSecurity SphincsSecurity.Security
set_option backward.isDefEq.respectTransparency false

namespace SphincsSecurity.QueryBudgetChecks

private def inconsistentBranch : OracleComp OracleWorld Unit := do
  let a ← liftM (OracleWorld.query (.inr []))
  let b ← liftM (OracleWorld.query (.inr []))
  if a = b then return ()
  else
    let _ ← liftM (OracleWorld.query (.inr [1]))
    return ()

example : ∀ result ∈ support ((simulateQ countedRomImpl inconsistentBranch).run.run' ∅), result.2 = (2 : Nat) := by
  have fresh : ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) []).run ∅ =
      (fun answer : HashOutput => (answer, (∅ : QueryCache HashSpec).cacheQuery [] answer)) <$>
        ($ᵗ HashOutput : ProbComp _) :=
    QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)
  have cached (answer : HashOutput) :
      ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) []).run ((∅ : QueryCache HashSpec).cacheQuery [] answer) =
        pure (answer, (∅ : QueryCache HashSpec).cacheQuery [] answer) :=
    QueryImpl.withCaching_run_some _ (by simp)
  intro result hr
  rw [← simulateQ_countHashQueries] at hr
  simp only [inconsistentBranch, countHashQueries, QueryCap.counted_query_bind, simulateQ_bind,
    simulateQ_spec_query, romImpl, QueryImpl.add_apply_inr, StateT.run'_eq, StateT.run_bind, fresh, bind_map_left, cached,
    pure_bind, ite_true, QueryCap.counted_pure, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, Nat.add_zero, Nat.reduceAdd, bind_pure_comp,
    simulateQ_map, StateT.run_map, Functor.map_map] at hr
  rw [support_map] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  rfl

example : ¬ inconsistentBranch.IsQueryBoundP (fun _ : OracleWorld.Domain => True) 2 := by
  intro h
  have h0 := (isQueryBoundP_query_bind_iff _ _ _ _).mp h
  have h1 := (isQueryBoundP_query_bind_iff _ _ _ _).mp (h0.2 (0 : HashOutput))
  have h2 := h1.2 (1 : HashOutput)
  have hne : (0 : HashOutput) ≠ 1 := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    change 0 = 1 at hn
    omega
  simp only [if_neg hne, if_true, Nat.reduceSub] at h2
  have h3 := (isQueryBoundP_query_bind_iff _ _ _ _).mp h2
  exact h3.1.elim (fun hfalse => hfalse (by decide)) (Nat.not_lt_zero _)

example {α : Type} (sample : ProbComp α) (cache : QueryCache HashSpec) :
    ((simulateQ countedRomImpl (liftM sample : OracleComp OracleWorld α)).run).run cache =
      (fun value => ((value, (0 : Nat)), cache)) <$> sample := by
  rw [← simulateQ_countHashQueries, countHashQueries_lift_prob, simulateQ_map, StateT.run_map,
    romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run]
  simp only [Functor.map_map]

private def repeatedSigning : QueryImpl SigningSpec (OracleComp OracleWorld) := fun _ => do
  let _ ← liftM (OracleWorld.query (.inr []))
  let _ ← liftM (OracleWorld.query (.inr []))
  return none

private def signingThenHashing : OracleComp (OracleWorld + SigningSpec) (HashOutput × HashOutput) := do
  let _ ← liftM ((OracleWorld + SigningSpec).query (.inr 0))
  let first ← liftM ((OracleWorld + SigningSpec).query (.inl (.inr [])))
  let second ← liftM ((OracleWorld + SigningSpec).query (.inl (.inr [])))
  return (first, second)

private noncomputable def mixedAccounting : OracleComp OracleWorld (Bool × HashQueries) := do
  let setup ← liftM (OracleWorld.query (.inr []))
  let ((observed, calls), log) ← countAdversary repeatedSigning signingThenHashing
  let (checked, verification) ← QueryCap.counted IsHash (do
    let answer ← liftM (OracleWorld.query (.inr []))
    pure answer : OracleComp OracleWorld HashOutput)
  return (decide (observed = (setup, setup) ∧ checked = setup ∧ log = [⟨0, none⟩]), ⟨calls, verification⟩)

/-- Repeated queries share cached answers and retain their call counts. -/
example : ∀ result ∈ support ((simulateQ romImpl mixedAccounting).run' ∅),
    result = ((true, ⟨2, 1⟩) : Bool × HashQueries) := by
  have fresh : ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) []).run ∅ =
      (fun answer : HashOutput => (answer, (∅ : QueryCache HashSpec).cacheQuery [] answer)) <$>
        ($ᵗ HashOutput : ProbComp _) :=
    QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)
  have cached (answer : HashOutput) :
      ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) []).run
        ((∅ : QueryCache HashSpec).cacheQuery [] answer) =
        pure (answer, (∅ : QueryCache HashSpec).cacheQuery [] answer) :=
    QueryImpl.withCaching_run_some _ (by simp)
  have forward (input : OracleWorld.Domain) :
      (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) input).run =
        (fun answer => (answer, ([] : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _) := rfl
  intro result hresult
  simp only [mixedAccounting, countAdversary, signingThenHashing, QueryCap.counted_query_bind,
    QueryCap.counted_pure, IsAdversaryHash, IsHash, if_true, if_false,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, forward,
    QueryImpl.withLogging_apply, repeatedSigning,
    WriterT.run_bind, WriterT.run_liftM, WriterT.run_pure, WriterT.run_tell,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, romImpl, pure_bind,
    bind_map_left, map_bind, map_pure, bind_assoc, fresh, cached,
    Nat.zero_add, Nat.add_zero, Nat.reduceAdd] at hresult
  simpa using hresult

end SphincsSecurity.QueryBudgetChecks
