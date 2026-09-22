import SphincsSecurity.Proof.Reference.FiniteHashWorld

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
attribute [local irreducible] hashInputs

noncomputable def fixedCacheWorld (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)
  | .inl sample => liftM (liftM (unifSpec.query sample) : ProbComp _)
  | .inr input => QueryImpl.withCaching (fun query => (pure (f query) : ProbComp _)) input

theorem fixedCacheWorld_some (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (h : cache input = some output) :
    (fixedCacheWorld f (.inr input)).run cache = pure (output, cache) := by
  rw [fixedCacheWorld, QueryImpl.withCaching_run_some _ h]

theorem fixedCacheWorld_none (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (input : HashInput) (h : cache input = none) :
    (fixedCacheWorld f (.inr input)).run cache = pure (f input, cache.cacheQuery input (f input)) := by
  rw [fixedCacheWorld, QueryImpl.withCaching_run_none _ h, map_pure]

theorem fixedCacheWorld_agrees (f : QueryImpl HashSpec Id) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hagrees : cache.AgreesWithFn f)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((fixedCacheWorld f input).run cache)) : result.2.AgreesWithFn f := by
  cases input with
  | inl sample =>
    change result ∈ support ((fun answer => (answer, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _)) at hresult
    rw [support_map] at hresult
    obtain ⟨answer, _, rfl⟩ := hresult
    exact hagrees
  | inr input =>
    cases hc : cache input with
    | some output =>
      rw [fixedCacheWorld_some f cache input output hc, mem_support_pure_iff] at hresult
      subst result
      exact hagrees
    | none =>
      rw [fixedCacheWorld_none f cache input hc, mem_support_pure_iff] at hresult
      subst result
      exact (QueryCache.agreesWithFn_cacheQuery_iff cache input (f input) f hc).mpr ⟨hagrees, rfl⟩

theorem fixedCacheWorld_run_agrees {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hagrees : cache.AgreesWithFn f)
    (result : α × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ (fixedCacheWorld f) computation).run cache)) : result.2.AgreesWithFn f := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
    subst result
    exact hagrees
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, htail⟩ := hresult
    exact ih step.1 step.2 (fixedCacheWorld_agrees f input cache hagrees step hstep) result htail

theorem fixedCacheWorld_query_forget (f : QueryImpl HashSpec Id) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hagrees : cache.AgreesWithFn f) :
    Prod.fst <$> (fixedCacheWorld f input).run cache = fixedHashWorld f input := by
  cases input with
  | inl sample => simp only [fixedCacheWorld, StateT.run_liftM, map_bind, map_pure, bind_pure, fixedHashWorld]
  | inr input =>
    cases hc : cache input with
    | some output => rw [fixedCacheWorld_some f cache input output hc, map_pure]; exact congrArg pure (hagrees hc).symm
    | none => rw [fixedCacheWorld_none f cache input hc, map_pure]; rfl

theorem fixedCacheWorld_run_forget {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hagrees : cache.AgreesWithFn f) :
    (simulateQ (fixedCacheWorld f) computation).run' cache = simulateQ (fixedHashWorld f) computation := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    trans (fixedCacheWorld f input).run cache >>= fun result => simulateQ (fixedHashWorld f) (next result.1)
    · apply bind_congr_of_forall_mem_support
      intro result hresult
      exact ih result.1 result.2 (fixedCacheWorld_agrees f input cache hagrees result hresult)
    · calc
        _ = (Prod.fst <$> (fixedCacheWorld f input).run cache) >>= fun answer =>
            simulateQ (fixedHashWorld f) (next answer) := by rw [bind_map_left]
        _ = _ := by rw [fixedCacheWorld_query_forget f input cache hagrees, simulateQ_bind, simulateQ_spec_query]

theorem fixedCacheWorld_support (f : QueryImpl HashSpec Id) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((fixedCacheWorld f input).run cache)) :
    result ∈ support ((romImpl input).run cache) := by
  cases input with
  | inl sample => exact hresult
  | inr input =>
    change result ∈ support ((randomOracle input).run cache)
    cases hc : cache input with
    | some output =>
      rw [fixedCacheWorld_some f cache input output hc, mem_support_pure_iff] at hresult
      subst result
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc]
      simp only [mem_support_pure_iff]
    | none =>
      rw [fixedCacheWorld_none f cache input hc, mem_support_pure_iff] at hresult
      subst result
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map]
      exact ⟨f input, mem_support_uniformSample _, rfl⟩

theorem fixedCacheWorld_run_support {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ (fixedCacheWorld f) computation).run cache)) :
    result ∈ support ((simulateQ romImpl computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value => simpa only [simulateQ_pure, StateT.run_pure] using hresult
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult ⊢
    obtain ⟨step, hstep, htail⟩ := hresult
    exact ⟨step, fixedCacheWorld_support f input cache step hstep, ih step.1 step.2 result htail⟩

theorem evalDist_romRun_cache_eq_finiteHash {α : Type} (computation : OracleComp OracleWorld α)
    (inputs : Finset HashInput) (hinputs : hashInputs computation ⊆ inputs) (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl computation).run cache] =
      𝒟[do
        let table ← sampleHashTable inputs
        (simulateQ (fixedCacheWorld (finiteHashAnswer cache inputs table)) computation).run cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact (evalDist_bind_const_neverFails _ (by simp [sampleHashTable]) (pure (value, cache))).symm
  | query_bind input next ih =>
    have hnext : ∀ output, hashInputs (next output) ⊆ inputs :=
      fun output => (hashInputs_next_subset input next output).trans hinputs
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    cases input with
    | inl sample =>
      change 𝒟[(liftM (unifSpec.query sample) : ProbComp _) >>= fun output =>
        (simulateQ romImpl (next output)).run cache] = _
      trans 𝒟[do
        let output ← (liftM (unifSpec.query sample) : ProbComp _)
        let table ← sampleHashTable inputs
        (simulateQ (fixedCacheWorld (finiteHashAnswer cache inputs table)) (next output)).run cache]
      · exact evalDist_bind_congr_left _ _ _ (fun output => ih output (hnext output) cache)
      · rw [evalDist_bind_comm]
        apply evalDist_bind_congr_left
        intro table
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, fixedCacheWorld,
          StateT.run_liftM, bind_assoc, pure_bind]
        rfl
    | inr input =>
      have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
      rw [show romImpl (.inr input) = randomOracle (spec := HashSpec) input from rfl]
      cases hcache : cache input with
      | some output =>
        rw [QueryImpl.withCaching_run_some _ hcache, pure_bind, ih output (hnext output) cache]
        apply evalDist_bind_congr_left
        intro table
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, fixedCacheWorld_some _ _ _ _ hcache, pure_bind]
      | none =>
        rw [QueryImpl.withCaching_run_none _ hcache, map_eq_bind_pure_comp]
        simp only [Function.comp, bind_assoc, pure_bind]
        trans 𝒟[do
          let output ← ($ᵗ HashOutput : ProbComp _)
          let table ← sampleHashTable inputs
          (simulateQ (fixedCacheWorld (finiteHashAnswer (cache.cacheQuery input output) inputs table))
            (next output)).run (cache.cacheQuery input output)]
        · exact evalDist_bind_congr_left _ _ _ (fun output => ih output (hnext output) _)
        · simp_rw [finiteHashAnswer_cacheQuery cache inputs _ input hin hcache]
          rw [sampleHashTable, ← evalDist_finiteHashTable_extract inputs (⟨input, hin⟩ : inputs)
            (fun table output => (simulateQ (fixedCacheWorld (finiteHashAnswer cache inputs table))
              (next output)).run (cache.cacheQuery input output))]
          apply evalDist_bind_congr_left
          intro table
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, fixedCacheWorld_none _ _ _ hcache,
            finiteHashAnswer_none cache inputs table input hin hcache, pure_bind]

end SphincsSecurity.Concrete
