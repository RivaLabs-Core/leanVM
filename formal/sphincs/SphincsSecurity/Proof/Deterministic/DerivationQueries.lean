import SphincsSecurity.Proof.Deterministic.DerivationTable

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def DerivationHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (∃ parameter domain, input = keygenHashInput parameter domain seed) ∨
    ∃ parameter message trial, input = randomizerHashInput parameter seed message trial

def IsDerivationQuery (input : HashInput) : Prop := ∃ seed, DerivationHit input seed

theorem DerivationHit.seedHit (input : HashInput) (seed : MasterSeed) (h : DerivationHit input seed) : SeedHit input seed := by
  rcases h with ⟨parameter, domain, rfl⟩ | ⟨parameter, message, trial, rfl⟩
  · exact derivationSeedHit_keygen parameter domain seed
  · exact derivationSeedHit_randomizer parameter seed message trial

theorem not_isDerivationQuery_tweakable (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    ¬IsDerivationQuery (tweakableHashInput parameter domain payload) := by
  rintro ⟨seed, h⟩
  rcases h with ⟨p, d, heq⟩ | ⟨p, message, trial, heq⟩
  · exact keygenHashInput_ne_tweakableHashInput p parameter d domain seed payload heq.symm
  · exact randomizerHashInput_ne_tweakableHashInput p parameter seed message trial domain payload heq.symm

theorem probEvent_derivationHit_le (input : HashInput) :
    Pr[DerivationHit input | sampleMasterSeed] ≤ 1 / ((2 ^ 256 : Nat) : ENNReal) :=
  (probEvent_mono (fun seed _ h => h.seedHit input seed)).trans (probEvent_seedHit_le input)

theorem signingDerivationCache_agreeOutside_derivation (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    AgreeOutside (fun input => DerivationHit input seed)
      (signingDerivationCache seed parameterOutput outputs randomizers) ∅ := by
  intro input hinput
  unfold signingDerivationCache
  rw [cacheTable_apply_of_not_mem]
  · unfold derivationCache
    rw [cacheTable_apply_of_not_mem]
    · apply QueryCache.cacheQuery_of_ne
      intro heq
      exact hinput (Or.inl ⟨0, .parameter, heq⟩)
    · intro position heq
      exact hinput (Or.inl ⟨truncateHash parameterOutput, secretDomain position, heq⟩)
  · intro position heq
    exact hinput (Or.inr ⟨truncateHash parameterOutput, position.1, position.2, heq⟩)

end SphincsSecurity.Seeded
