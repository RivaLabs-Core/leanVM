import SphincsSecurity.Proof.Deterministic.GameExpansion
import SphincsSecurity.Proof.Adversary.CountedTrace

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α : Type}

theorem Erases.simulateQ {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (known : QueryCache target) (left right : QueryImpl source (OracleComp target))
    (himpl : ∀ input, Erases known (left input) (right input)) (computation : OracleComp source α) :
    Erases known (simulateQ left computation) (simulateQ right computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (himpl input).bind _ _ ih

noncomputable def interfaceAfterParameter
    (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (parameter : PublicParameter) (seed : MasterSeed) : OracleComp OracleWorld α := do
  let root ← liftM (treeRoot parameter topLayer Concrete.rootTree seed : OracleComp HashSpec Digest)
  simulateQ (Security.expandSigning (fun message => liftM (sign ⟨seed, parameter, root⟩ message : OracleComp HashSpec _)))
    (source ⟨root, parameter⟩)

noncomputable def tableInterfaceAfterParameter
    (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (parameter : PublicParameter) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) : OracleComp OracleWorld α := do
  let root ← liftM (Concrete.treeRoot parameter topLayer Concrete.rootTree (tableOts outputs topLayer Concrete.rootTree) :
    OracleComp HashSpec Digest)
  simulateQ (Security.expandSigning (fun message => liftM (tableSign randomizers (tableKey parameter root outputs) message : OracleComp HashSpec _)))
    (source ⟨root, parameter⟩)

theorem erases_interfaceAfterParameter (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α) :
    Erases (worldKnown known) (interfaceAfterParameter source parameter seed)
      (tableInterfaceAfterParameter source parameter outputs randomizers) := by
  unfold interfaceAfterParameter tableInterfaceAfterParameter
  apply (erases_treeRoot known parameter seed outputs hsecrets topLayer Concrete.rootTree).lift_hash.bind
  intro root
  apply Erases.simulateQ
  intro input
  cases input with
  | inl world => exact .refl _ _
  | inr message => exact (erases_deterministicSign known parameter seed root outputs randomizers hsecrets hrandomizers message).lift_hash

attribute [local irreducible] interfaceAfterParameter tableInterfaceAfterParameter signingDerivationCache

theorem evalDist_interfaceAfterParameter_prepared
    (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (seed : MasterSeed) (parameterOutput : HashOutput) :
    𝒟[(simulateQ romImpl (interfaceAfterParameter source (truncateHash parameterOutput) seed)).run'
      (parameterCache seed parameterOutput)] =
    𝒟[do
      let outputs ← sampleSecretOutputs
      let randomizers ← sampleRandomizerOutputs
      (simulateQ romImpl (tableInterfaceAfterParameter source (truncateHash parameterOutput) outputs randomizers)).run'
        (signingDerivationCache seed parameterOutput outputs randomizers)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareSecrets (truncateHash parameterOutput) seed) : OracleComp OracleWorld SecretOutputs)]
  rw [show simulateQ romImpl (liftM (prepareSecrets (truncateHash parameterOutput) seed) : OracleComp OracleWorld SecretOutputs) =
      simulateQ randomOracle (prepareSecrets (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareSecrets, ← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr'
  intro outputs
  rw [evalDist_presample_computation _
    (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs)]
  rw [show simulateQ romImpl (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs) =
      simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareRandomizers, ← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr'
  intro randomizers
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  exact congrArg _ ((erases_interfaceAfterParameter _ _ seed outputs randomizers
    (signingDerivationCache_secret seed parameterOutput outputs randomizers)
    (signingDerivationCache_randomizer seed parameterOutput outputs randomizers) source).evalDist_run _ le_rfl)

noncomputable def interfaceGame (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α) : OracleComp OracleWorld α := do
  let seed ← liftM sampleMasterSeed
  let parameter ← liftM (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)
  interfaceAfterParameter source parameter seed

noncomputable def programmedInterfaceGame (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α) : ProbComp α := do
  let seed ← sampleMasterSeed
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← sampleSecretOutputs
  let randomizers ← sampleRandomizerOutputs
  (simulateQ romImpl (tableInterfaceAfterParameter source (truncateHash parameterOutput) outputs randomizers)).run'
    (signingDerivationCache seed parameterOutput outputs randomizers)

theorem evalDist_interfaceGame_programmed (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α) :
    𝒟[(simulateQ romImpl (interfaceGame source)).run' ∅] = 𝒟[programmedInterfaceGame source] := by
  rw [interfaceGame, run'_lift_sample_bind]
  unfold programmedInterfaceGame
  apply evalDist_bind_congr'
  intro seed
  rw [run'_lift_hash_bind, run_deriveParameter, bind_map_left]
  exact evalDist_bind_congr' _ (evalDist_interfaceAfterParameter_prepared source seed)

theorem countedGameCore_eq_interfaceGame (adversary : Security.Adversary) :
    (fun result => (result.1, result.2.total)) <$> Security.countedGameCore adversary =
      interfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk)) := by
  rw [Security.countedGameCore_eq_trace]
  simp only [interfaceGame, interfaceAfterParameter, keygenFromSeed, bind_assoc, pure_bind, liftM_bind, liftM_pure]


theorem counted_experiment_programmed (adversary : Security.Adversary) :
    𝒟[(fun result => (result.1, result.2.total)) <$> Security.experiment adversary] =
      𝒟[programmedInterfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))] := by
  have heq := congrArg (fun computation => (simulateQ romImpl computation).run' ∅)
    (countedGameCore_eq_interfaceGame adversary)
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map] at heq
  have hsource : (fun result => (result.1, result.2.total)) <$> Security.experiment adversary =
      (simulateQ romImpl (interfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk)))).run' ∅ := by
    simpa only [Security.experiment, StateT.run'_eq, Functor.map_map, romImpl] using heq
  rw [hsource, evalDist_interfaceGame_programmed]

attribute [local irreducible] Security.experiment Security.HashQueries.total

set_option linter.constructorNameAsVariable false in
theorem programmedInterface_budget (adversary : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound adversary q) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (result : Bool × Nat)
    (hresult : result ∈ support ((simulateQ romImpl (tableInterfaceAfterParameter
      (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))
      (truncateHash parameterOutput) outputs randomizers)).run'
        (signingDerivationCache seed parameterOutput outputs randomizers))) : result.2 ≤ q := by
  have hprogrammed : result ∈ support (programmedInterfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
      (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))) := by
    simp only [programmedInterfaceGame, mem_support_bind_iff]
    refine ⟨seed, ?_, parameterOutput, mem_support_uniformSample _, outputs, ?_, randomizers, ?_, hresult⟩
    · rw [mem_support_iff]
      unfold sampleMasterSeed
      rw [probOutput_uniformSample]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    · rw [mem_support_iff]
      unfold sampleSecretOutputs
      rw [probOutput_uniformSample]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    · rw [mem_support_iff]
      unfold sampleRandomizerOutputs
      rw [probOutput_uniformSample]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  rw [← mem_support_iff_of_evalDist_eq (counted_experiment_programmed adversary), support_map] at hprogrammed
  obtain ⟨record, hrecord, rfl⟩ := hprogrammed
  rw [Security.HasHashQueryBound] at hbound
  exact hbound record hrecord

end SphincsSecurity.Seeded
