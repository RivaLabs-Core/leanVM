import SphincsSecurity.Proof.Deterministic.DerivationGuessing
import SphincsSecurity.Proof.Seeded.SelectedQueryBound

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def prependDerivation (input : OracleWorld.Domain) (inputs : List HashInput) : List HashInput :=
  if hashBad IsDerivationQuery input then prependHash input inputs else inputs

theorem prependDerivation_length (input : OracleWorld.Domain) (inputs : List HashInput) :
    (prependDerivation input inputs).length = inputs.length + if hashBad IsDerivationQuery input then 1 else 0 := by
  cases input with
  | inl sample => simp [prependDerivation, hashBad]
  | inr input =>
    by_cases hinput : IsDerivationQuery input <;> simp [prependDerivation, hashBad, prependHash, hinput]

theorem prependDerivation_avoid (input : OracleWorld.Domain) (inputs : List HashInput)
    (seed : MasterSeed) (hseed : ¬SeedHitLog (prependDerivation input inputs) seed) :
    ¬hashBad (fun input => DerivationHit input seed) input ∧ ¬SeedHitLog inputs seed := by
  cases input with
  | inl sample => simpa only [prependDerivation, hashBad, if_false, not_false_eq_true, true_and] using hseed
  | inr input =>
    by_cases hinput : IsDerivationQuery input
    · have havoid : ¬SeedHit input seed ∧ ¬SeedHitLog inputs seed := by
        simpa only [prependDerivation, hashBad, if_pos hinput, prependHash, SeedHitLog,
          List.mem_cons, exists_eq_or_imp, not_or] using hseed
      exact ⟨fun h => havoid.1 (h.seedHit input seed), havoid.2⟩
    · exact ⟨fun h => hinput ⟨seed, h⟩, by simpa only [prependDerivation, hashBad, if_neg hinput] using hseed⟩

theorem derivationQueryBound_of_seed_caches {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (inputs : List HashInput) (caches : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hsize : inputs.length + q < 2 ^ 256)
    (hagree : ∀ seed, ¬SeedHitLog inputs seed → AgreeOutside (fun input => DerivationHit input seed) (caches seed) cache)
    (hbound : ∀ seed, ¬SeedHitLog inputs seed → SelectedQueryBound (hashBad IsDerivationQuery) computation (caches seed) q) :
    SelectedQueryBound (hashBad IsDerivationQuery) computation cache q := by
  induction computation using OracleComp.inductionOn generalizing q inputs caches cache with
  | pure value =>
    intro result hresult
    simp only [QueryCap.counted_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
      map_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Nat.zero_le q
  | query_bind input next ih =>
    obtain ⟨seed, hseed⟩ := exists_seed_not_hit inputs (by omega)
    obtain ⟨step, hstep⟩ := probComp_support_nonempty ((romImpl input).run (caches seed))
    have hcost := (selectedQueryBound_query_bind (hashBad IsDerivationQuery) input next (caches seed) q
      (hbound seed hseed) step hstep).1
    apply selectedQueryBound_query_bind_of (hashBad IsDerivationQuery) input next cache q hcost
    intro result hresult
    have hcache := romImpl_support_cacheAfter input cache result hresult
    rcases result with ⟨answer, nextCache⟩
    dsimp at hcache
    subst nextCache
    have htransfer (seed : MasterSeed) (hseed : ¬SeedHitLog (prependDerivation input inputs) seed) :=
      romImpl_support_transfer (fun input => DerivationHit input seed) (caches seed) cache
        (hagree seed (prependDerivation_avoid input inputs seed hseed).2) input
        (prependDerivation_avoid input inputs seed hseed).1 answer hresult
    apply ih answer (q - (if hashBad IsDerivationQuery input then 1 else 0))
      (prependDerivation input inputs) (fun seed => cacheAfter (caches seed) input answer) (cacheAfter cache input answer)
    · rw [prependDerivation_length]
      omega
    · intro seed hseed
      exact (htransfer seed hseed).2
    · intro seed hseed
      exact (selectedQueryBound_query_bind (hashBad IsDerivationQuery) input next (caches seed) q
        (hbound seed (prependDerivation_avoid input inputs seed hseed).2) _ (htransfer seed hseed).1).2


theorem support_property_of_seed_caches {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (inputs : List HashInput) (caches : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hsize : inputs.length + q < 2 ^ 256)
    (hagree : ∀ seed, ¬SeedHitLog inputs seed → AgreeOutside (fun input => DerivationHit input seed) (caches seed) cache)
    (hbound : SelectedQueryBound (hashBad IsDerivationQuery) computation cache q)
    (property : α → Prop)
    (hproperty : ∀ seed, ¬SeedHitLog inputs seed → ∀ result ∈ support ((simulateQ romImpl computation).run' (caches seed)), property result) :
    ∀ result ∈ support ((simulateQ romImpl computation).run' cache), property result := by
  induction computation using OracleComp.inductionOn generalizing q inputs caches cache with
  | pure value =>
    intro result hresult
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, mem_support_pure_iff] at hresult
    subst result
    obtain ⟨seed, hseed⟩ := exists_seed_not_hit inputs (by omega)
    exact hproperty seed hseed value (by simp)
  | query_bind input next ih =>
    intro result hresult
    rw [run'_query_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    have hcost := selectedQueryBound_query_bind (hashBad IsDerivationQuery) input next cache q hbound step hstep
    have hcache := romImpl_support_cacheAfter input cache step hstep
    rcases step with ⟨answer, nextCache⟩
    dsimp at hcache
    subst nextCache
    have htransfer (seed : MasterSeed) (hseed : ¬SeedHitLog (prependDerivation input inputs) seed) :=
      romImpl_support_transfer (fun input => DerivationHit input seed) (caches seed) cache
        (hagree seed (prependDerivation_avoid input inputs seed hseed).2) input
        (prependDerivation_avoid input inputs seed hseed).1 answer hstep
    apply ih answer (q - (if hashBad IsDerivationQuery input then 1 else 0))
      (prependDerivation input inputs) (fun seed => cacheAfter (caches seed) input answer) (cacheAfter cache input answer)
      _ _ hcost.2 _ result htail
    · rw [prependDerivation_length]
      omega
    · intro seed hseed
      exact (htransfer seed hseed).2
    · intro seed hseed result hresult
      apply hproperty seed (prependDerivation_avoid input inputs seed hseed).2 result
      rw [run'_query_bind, mem_support_bind_iff]
      exact ⟨(answer, cacheAfter (caches seed) input answer), (htransfer seed hseed).1, hresult⟩

end SphincsSecurity.Seeded
