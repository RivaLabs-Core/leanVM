import SphincsSecurity.Proof.Deterministic.InterfaceGameExpansion
import SphincsSecurity.Proof.Deterministic.TableHashDomains
import SphincsSecurity.Proof.Reference.InterfaceCounting
import SphincsSecurity.Proof.Deterministic.DerivationBudgetTransfer

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {α : Type}

def IsInterfaceDerivation : (OracleWorld + SigningSpec).Domain → Prop
  | .inl world => hashBad IsDerivationQuery world
  | .inr _ => False

theorem isInterfaceDerivation_hash (input : (OracleWorld + SigningSpec).Domain)
    (h : IsInterfaceDerivation input) : Security.IsAdversaryHash input := by
  cases input with
  | inr message => exact False.elim h
  | inl world => cases world with
    | inl sample => exact False.elim h
    | inr query => trivial

theorem counted_tableSigning (randomizers : RandomizerOutputs) (key : SphincsSecurity.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    QueryCap.counted (hashBad IsDerivationQuery)
      (simulateQ (Security.expandSigning (fun message => liftM (tableSign randomizers key message : OracleComp HashSpec _))) computation) =
    simulateQ (Security.expandSigning (fun message => liftM (tableSign randomizers key message : OracleComp HashSpec _)))
      (QueryCap.counted IsInterfaceDerivation computation) := by
  apply QueryCap.counted_simulateQ
  intro input
  cases input with
  | inl world =>
    change QueryCap.counted (hashBad IsDerivationQuery) (liftM (OracleWorld.query world) : OracleComp OracleWorld _) =
      (fun value => (value, if IsInterfaceDerivation (.inl world) then 1 else 0)) <$> (liftM (OracleWorld.query world) : OracleComp OracleWorld _)
    by_cases h : hashBad IsDerivationQuery world <;>
      simpa only [IsInterfaceDerivation, h, if_true, if_false] using QueryCap.counted_query (hashBad IsDerivationQuery) world
  | inr message => simpa [Security.expandSigning, IsInterfaceDerivation, SigningSpec, OracleWorld] using (derivationFree_tableSign randomizers key message).lift_world.counted

theorem tableInterface_derivation_count_le
    (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α)
    (parameter : PublicParameter) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (cache : QueryCache HashSpec) (result : ((α × Nat) × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (QueryCap.counted (hashBad IsDerivationQuery)
      (tableInterfaceAfterParameter (fun pk => QueryCap.counted Security.IsAdversaryHash (source pk))
        parameter outputs randomizers))).run cache)) : result.1.2 ≤ result.1.1.2 := by
  rw [tableInterfaceAfterParameter, QueryCap.counted_bind,
    (derivationFree_treeRoot parameter topLayer Concrete.rootTree _).lift_world.counted] at hresult
  simp only [bind_map_left, Nat.zero_add, bind_pure_comp, Prod.mk.eta] at hresult
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨root, hroot, htail⟩ := hresult
  rw [counted_tableSigning] at htail
  simp only [id_map'] at htail
  rw [← QueryImpl.simulateQ_compose] at htail
  exact QueryCap.counted_support_mono IsInterfaceDerivation Security.IsAdversaryHash isInterfaceDerivation_hash
    _ (source ⟨root.1, parameter⟩) root.2 result htail

attribute [local irreducible] tableInterfaceAfterParameter Security.HashQueries.total Security.experiment

theorem programmedInterface_derivation_budget (adversary : Security.Adversary) (q : Nat)
    (hbound : Security.HasHashQueryBound adversary q) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    SelectedQueryBound (hashBad IsDerivationQuery)
      (tableInterfaceAfterParameter (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))
        (truncateHash parameterOutput) outputs randomizers)
      (signingDerivationCache seed parameterOutput outputs randomizers) q := by
  rw [selectedQueryBound_iff_run]
  intro result hresult
  apply (tableInterface_derivation_count_le _ _ _ _ _ result hresult).trans
  apply programmedInterface_budget adversary q hbound seed parameterOutput outputs randomizers result.1.1
  have hforget := congrArg (fun computation => (simulateQ romImpl computation).run'
    (signingDerivationCache seed parameterOutput outputs randomizers))
    (QueryCap.counted_forget (hashBad IsDerivationQuery)
      (tableInterfaceAfterParameter (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))
        (truncateHash parameterOutput) outputs randomizers))
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at hforget
  rw [← hforget, support_map]
  exact ⟨result, hresult, rfl⟩

theorem tableInterface_derivation_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameterOutput : HashOutput) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    SelectedQueryBound (hashBad IsDerivationQuery)
      (tableInterfaceAfterParameter (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))
        (truncateHash parameterOutput) outputs randomizers) ∅ q :=
  derivationQueryBound_of_seed_caches _ q []
    (fun seed => signingDerivationCache seed parameterOutput outputs randomizers) ∅
    (by simpa only [List.length_nil, Nat.zero_add] using hsmall)
    (fun seed _ => signingDerivationCache_agreeOutside_derivation seed parameterOutput outputs randomizers)
    (fun seed _ => programmedInterface_derivation_budget adversary q hbound seed parameterOutput outputs randomizers)

theorem tableInterface_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (parameterOutput : HashOutput) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    ∀ result ∈ support ((simulateQ romImpl (tableInterfaceAfterParameter
      (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))
      (truncateHash parameterOutput) outputs randomizers)).run' ∅), result.2 ≤ q := by
  have hselected := tableInterface_derivation_budget adversary q hsmall hbound parameterOutput outputs randomizers
  exact support_property_of_seed_caches _ q []
    (fun seed => signingDerivationCache seed parameterOutput outputs randomizers) ∅ (by simpa only [List.length_nil, Nat.zero_add] using hsmall)
    (fun seed _ => signingDerivationCache_agreeOutside_derivation seed parameterOutput outputs randomizers)
    hselected (fun result => result.2 ≤ q)
    (fun seed _ => programmedInterface_budget adversary q hbound seed parameterOutput outputs randomizers)

end SphincsSecurity.Seeded
