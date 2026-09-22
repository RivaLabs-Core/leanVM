import SphincsSecurity.Proof.RandomizedStatement

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Seeded.keygenFromSeed Seeded.sign experiment
attribute [local irreducible] SigningTranscript.Valid SigningTranscript.Contains

theorem run_counted_adversary_forget {α : Type} (sk : Seeded.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle sk) (QueryCap.counted IsAdversaryHash computation)).run =
      (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle sk) computation).run := by
  have h := congrArg (fun c : OracleComp (OracleWorld + SigningSpec) α =>
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
      signingOracle sk) c).run) (QueryCap.counted_forget IsAdversaryHash computation)
  simpa only [simulateQ_map, WriterT.run_map, Prod.map] using h

theorem countedGameCore_forget (adversary : Adversary) :
    Prod.fst <$> countedGameCore adversary = gameCore adversary := by
  unfold countedGameCore gameCore countAdversary
  simp only [map_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  rintro ⟨pk, sk⟩
  rw [← run_counted_adversary_forget sk (adversary.main pk), bind_map_left]
  apply bind_congr
  rintro ⟨⟨forgery, calls⟩, log⟩
  simp only [map_pure, bind_pure_comp]
  have h := QueryCap.counted_forget IsHash
    (liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  simpa only [Functor.map_map] using congrArg
    (Functor.map (Bool.and (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery)))) h

theorem experiment_forget (adversary : Adversary) :
    Prod.fst <$> experiment adversary = (simulateQ romImpl (gameCore adversary)).run' ∅ := by
  unfold experiment
  change Prod.fst <$> (simulateQ romImpl (countedGameCore adversary)).run' ∅ = _
  rw [← StateT.run'_map', ← simulateQ_map, countedGameCore_forget]

/-- Erasing the counters preserves the winning probability. -/
theorem advantage_eq_uncounted (adversary : Adversary) :
    forgeAdvantage adversary = Pr[= true | (simulateQ romImpl (gameCore adversary)).run' ∅] := by
  have h := congrArg (fun law : ProbComp Bool => Pr[fun result => result = true | law])
    (experiment_forget adversary)
  simp only [probEvent_map, Function.comp_def] at h
  simpa only [forgeAdvantage, probEvent_eq_eq_probOutput] using h

end SphincsSecurity.Security
