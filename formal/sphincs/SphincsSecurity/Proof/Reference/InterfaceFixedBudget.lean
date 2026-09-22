import SphincsSecurity.Proof.Deterministic.InterfaceReference
import SphincsSecurity.Proof.Reference.FixedQueryBound
import SphincsSecurity.Proof.Fts.FtsProbeSampling

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

variable {α : Type}

theorem fixedHashWorld_lift_hash_eq_pure (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      pure (evalWithAnswerFn f computation) := by
  have h := fixedBoundaryRun_forget 0 f (liftM computation : OracleComp OracleWorld α)
  rw [fixedBoundaryRun_lift_hash, map_pure, boundaryEval_fst] at h
  exact h.symm

theorem fixedInterface_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameter : PublicParameter) (otsSecret : Seeded.OtsSecrets) (ftsSecret : Seeded.FtsSecrets)
    (f : QueryImpl HashSpec Id) :
    let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
    let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
    ∀ result ∈ support (simulateQ (fixedHashWorld f)
      (simulateQ (Security.expandSigning (sign key)) (QueryCap.counted Security.IsAdversaryHash
        (Seeded.sourceGame ⟨root, parameter⟩ (Seeded.memoAdversary (Security.embed adversary)))))),
      result.2 ≤ q := by
  dsimp only
  intro result hresult
  apply Seeded.randomizedInterface_counted_budget adversary q hsmall hbound parameter otsSecret ftsSecret result
  apply fixedHashWorld_support_rom f
  simpa only [Seeded.randomizedInterfaceAfterSecrets, simulateQ_bind,
    fixedHashWorld_lift_hash_eq_pure, pure_bind] using hresult

theorem fixedInterface_retained_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameter : PublicParameter) (otsSecret : Seeded.OtsSecrets) (ftsSecret : Seeded.FtsSecrets)
    (f : QueryImpl HashSpec Id) :
    let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
    let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
    ∀ result ∈ support (simulateQ (fixedHashWorld f)
      (simulateQ (Security.expandSigning (sign key)) (QueryCap.counted Security.IsAdversaryHash
        (FtsProbeSimulation.retainedGameRestComputation
          (Seeded.memoAdversary (Security.embed adversary)) ⟨root, parameter⟩)))), result.2 ≤ q := by
  dsimp only
  intro result hresult
  have h := fixedInterface_counted_budget adversary q hsmall hbound parameter otsSecret ftsSecret f
  simp_rw [Seeded.sourceGame_eq_traced, ← FtsProbeSimulation.retainedGameRestComputation_verdict_projection,
    QueryCap.counted_map, simulateQ_map, support_map] at h
  exact h _ ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete
