import SphincsSecurity.Proof.Deterministic.InterfaceDerivationCount
import SphincsSecurity.Proof.Deterministic.GameComparison

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def independentInterfaceGame {α : Type} (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α) : ProbComp α := do
  let material ← drawSigningMaterial
  (simulateQ romImpl (tableInterfaceAfterParameter source (truncateHash material.1) material.2.1 material.2.2)).run' ∅

theorem evalDist_programmedInterfaceGame_seed_last {α : Type}
    (source : PublicKey → OracleComp (OracleWorld + SigningSpec) α) :
    𝒟[programmedInterfaceGame source] = 𝒟[do
      let material ← drawSigningMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (tableInterfaceAfterParameter source (truncateHash material.1) material.2.1 material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] := by
  have heq : programmedInterfaceGame source = (do
      let seed ← sampleMasterSeed
      let material ← drawSigningMaterial
      (simulateQ romImpl (tableInterfaceAfterParameter source (truncateHash material.1) material.2.1 material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)) := by
    simp only [programmedInterfaceGame, drawSigningMaterial, bind_assoc, pure_bind]
  rw [heq, evalDist_bind_bind_swap]

attribute [local irreducible] Security.experiment programmedInterfaceGame tableInterfaceAfterParameter

theorem forgeAdvantage_le_independentInterface (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q) :
    Security.forgeAdvantage adversary ≤
      Pr[fun result => result.1 = true | independentInterfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
        (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))] +
      (q : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) := by
  let source := fun pk => QueryCap.counted Security.IsAdversaryHash
    (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk)
  have hsource : Security.forgeAdvantage adversary = Pr[fun result => result.1 = true | programmedInterfaceGame source] := by
    have h : Pr[fun result => result.1 = true | (fun result => (result.1, result.2.total)) <$> Security.experiment adversary] =
        Pr[fun result => result.1 = true | programmedInterfaceGame source] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (counted_experiment_programmed adversary)
    simpa only [probEvent_map, Function.comp_def, Security.forgeAdvantage] using h
  rw [hsource]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_programmedInterfaceGame_seed_last source)]
  unfold independentInterfaceGame
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_derivation_cache_change_le _
    (fun seed => signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
    (fun seed => signingDerivationCache_agreeOutside_derivation seed _ _ _) q
    (tableInterface_derivation_budget adversary q hsmall hbound material.1 material.2.1 material.2.2)
    (fun result => result.1 = true)

theorem independentInterface_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q) :
    ∀ result ∈ support (independentInterfaceGame (fun pk => QueryCap.counted Security.IsAdversaryHash
      (Concrete.FtsProbeSimulation.tracedGameRestComputation (Security.embed adversary) pk))), result.2 ≤ q := by
  intro result hresult
  rw [independentInterfaceGame, mem_support_bind_iff] at hresult
  obtain ⟨material, _, hresult⟩ := hresult
  exact tableInterface_counted_budget adversary q hsmall hbound material.1 material.2.1 material.2.2 result hresult

end SphincsSecurity.Seeded
