import SphincsSecurity.Proof.Deterministic.InterfaceMemo
import SphincsSecurity.Proof.Deterministic.ReferenceDistribution

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α State : Type}

noncomputable def randomizedInterfaceAfterSecrets (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (parameter : PublicParameter) (otsSecret : OtsSecrets) (ftsSecret : FtsSecrets) : OracleComp OracleWorld α := do
  let root ← liftM (Concrete.treeRoot parameter topLayer Concrete.rootTree (otsSecret topLayer Concrete.rootTree) : OracleComp HashSpec Digest)
  simulateQ (Security.expandSigning (Concrete.sign ⟨parameter, root, otsSecret, ftsSecret⟩)) (source ⟨root, parameter⟩)

theorem tableInterface_run' (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (parameter : PublicParameter) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (tableInterfaceAfterParameter source parameter outputs randomizers)).run' cache = (do
      let root ← (simulateQ randomOracle (Concrete.treeRoot parameter topLayer Concrete.rootTree (tableOts outputs topLayer Concrete.rootTree))).run cache
      evaluateSource (tableSign randomizers (tableKey parameter root.1 outputs)) (source ⟨root.1, parameter⟩) root.2) := by
  rw [tableInterfaceAfterParameter, run'_lift_hash_bind]
  rfl

theorem tableInterface_memo_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameterOutput : HashOutput) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    ∀ result ∈ support ((simulateQ romImpl (tableInterfaceAfterParameter
      (fun pk => QueryCap.counted Security.IsAdversaryHash (sourceGame pk (memoAdversary (Security.embed adversary))))
      (truncateHash parameterOutput) outputs randomizers)).run' ∅), result.2 ≤ q := by
  intro result hresult
  rw [tableInterface_run', mem_support_bind_iff] at hresult
  obtain ⟨root, hroot, hresult⟩ := hresult
  apply evaluateSource_counted_memo_budget _ _ _ root.2 q _ result hresult
  intro original horiginal
  apply tableInterface_counted_budget adversary q hsmall hbound parameterOutput outputs randomizers original
  simp_rw [← sourceGame_eq_traced]
  rw [tableInterface_run', mem_support_bind_iff]
  exact ⟨root, hroot, horiginal⟩

theorem evalDist_tableInterface_memo_counted (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : SecretOutputs) (state : State) :
    𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableInterfaceAfterParameter
        (fun pk => QueryCap.counted Security.IsAdversaryHash (sourceGame pk (memoAdversary adversary)))
        parameter outputs randomizers)).run state] =
    𝒟[(simulateQ (worldHandler hash) (randomizedInterfaceAfterSecrets
      (fun pk => QueryCap.counted Security.IsAdversaryHash (sourceGame pk (memoAdversary adversary)))
      parameter (tableOts outputs) (tableFts outputs))).run state] := by
  unfold tableInterfaceAfterParameter randomizedInterfaceAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply evalDist_bind_congr'
  intro root
  have h := evalDist_tableRequests hash (tableKey parameter root.1 outputs)
    (QueryCap.counted Security.IsAdversaryHash (sourceGame ⟨root.1, parameter⟩ (memoAdversary adversary)))
    ((freshRequests_sourceGame_memo _ _).counted Security.IsAdversaryHash) root.2
  rw [← simulateQ_runWorldSigning] at h
  exact h

theorem randomizedInterface_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameter : PublicParameter) (otsSecret : OtsSecrets) (ftsSecret : FtsSecrets) :
    ∀ result ∈ support ((simulateQ romImpl (randomizedInterfaceAfterSecrets
      (fun pk => QueryCap.counted Security.IsAdversaryHash (sourceGame pk (memoAdversary (Security.embed adversary))))
      parameter otsSecret ftsSecret)).run' ∅), result.2 ≤ q := by
  let outputs : SecretOutputs := secretHalves.symm ((otsSecret, ftsSecret), (fun _ _ _ _ => 0, fun _ _ _ => 0))
  have h := evalDist_tableInterface_memo_counted randomOracle (Security.embed adversary) parameter outputs ∅
  have hmap := congrArg (Functor.map Prod.fst) h
  simp only [evalDist_bind, map_bind, worldHandler_randomOracle] at hmap
  intro result hresult
  have heq : 𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ romImpl (tableInterfaceAfterParameter
        (fun pk => QueryCap.counted Security.IsAdversaryHash (sourceGame pk (memoAdversary (Security.embed adversary))))
        parameter outputs randomizers)).run' ∅] =
      𝒟[(simulateQ romImpl (randomizedInterfaceAfterSecrets
        (fun pk => QueryCap.counted Security.IsAdversaryHash (sourceGame pk (memoAdversary (Security.embed adversary))))
        parameter otsSecret ftsSecret)).run' ∅] := by
    simpa only [StateT.run'_eq, evalDist_bind, evalDist_map, outputs, tableOts_from_halves, tableFts_from_halves] using hmap
  rw [← mem_support_iff_of_evalDist_eq heq, mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  have hb := tableInterface_memo_counted_budget adversary q hsmall hbound (outputHalves.symm (parameter, 0)) outputs randomizers
  simp only [truncate_from_halves] at hb
  exact hb result hresult


theorem tableInterface_counted_forget (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (parameter : PublicParameter) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    Prod.fst <$> tableInterfaceAfterParameter (fun pk => QueryCap.counted Security.IsAdversaryHash (source pk)) parameter outputs randomizers =
      tableInterfaceAfterParameter source parameter outputs randomizers := by
  simp only [tableInterfaceAfterParameter, map_bind, ← simulateQ_map, QueryCap.counted_forget]

theorem tableInterface_sourceGame (adversary : Adversary) (parameter : PublicParameter)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    tableInterfaceAfterParameter (fun pk => sourceGame pk adversary) parameter outputs randomizers =
      tableGameAfterParameter adversary parameter outputs randomizers := by
  unfold tableInterfaceAfterParameter tableGameAfterParameter
  apply bind_congr
  intro root
  exact runSigning_sourceGame randomizers (tableKey parameter root outputs) ⟨root, parameter⟩ adversary

theorem independentInterface_forget (adversary : Adversary) :
    Prod.fst <$> independentInterfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
      (Concrete.FtsProbeSimulation.tracedGameRestComputation adversary pk)) = independentTableGame adversary := by
  simp_rw [← sourceGame_eq_traced]
  rw [independentInterfaceGame, independentTableGame, map_bind]
  apply bind_congr
  intro material
  rw [← StateT.run'_map', ← simulateQ_map, tableInterface_counted_forget, tableInterface_sourceGame]

theorem forgeAdvantage_le_randomizedReference (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q) :
    Security.forgeAdvantage adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary (Security.embed adversary)) +
      (q : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) := by
  have h := forgeAdvantage_le_independentInterface adversary q hsmall hbound
  have hforget := congrArg (fun law => Pr[= true | law]) (independentInterface_forget (Security.embed adversary))
  rw [probOutput_map] at hforget
  rw [hforget] at h
  have hmemo := prob_independentTableGame_le_memo (Security.embed adversary)
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo (Security.embed adversary))] at hmemo
  exact h.trans (add_le_add hmemo le_rfl)

end SphincsSecurity.Seeded
