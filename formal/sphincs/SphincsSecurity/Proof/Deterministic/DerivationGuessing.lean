import SphincsSecurity.Proof.Deterministic.DerivationQueries
import SphincsSecurity.Proof.Seeded.AdaptiveSeedGuessing
import SphincsSecurity.Proof.Reference.QueryAllocation

namespace SphincsSecurity.Seeded

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem traceHashes_selected_count {α : Type} (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, QueryCap.calls selected result.2)) <$> traceHashes computation =
      QueryCap.counted (hashBad selected) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [traceHashes_query_bind, QueryCap.counted_query_bind, map_bind, map_pure]
    congr 1
    funext answer
    rw [← ih answer]
    simp only [bind_pure_comp, Functor.map_map]
    congr 1
    funext result
    cases input <;> simp only [prependHash, hashBad, QueryCap.calls_cons, if_false, Nat.zero_add]

theorem traceHashes_selected_le {α : Type} (selected : HashInput → Prop) [DecidablePred selected]
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (QueryCap.counted (hashBad selected) computation)).run' cache), result.2 ≤ q)
    (result : α × List HashInput)
    (hresult : result ∈ support ((simulateQ romImpl (traceHashes computation)).run' cache)) :
    QueryCap.calls selected result.2 ≤ q := by
  apply hbound (result.1, QueryCap.calls selected result.2)
  rw [← traceHashes_selected_count, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, support_map]
  rw [StateT.run'_eq, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact ⟨record, hrecord, rfl⟩

theorem probEvent_derivationHitLog_le (inputs : List HashInput) :
    Pr[fun seed => TraceHits (fun input => DerivationHit input seed) inputs | sampleMasterSeed] ≤
      (QueryCap.calls IsDerivationQuery inputs : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) := by
  induction inputs with
  | nil => simp [TraceHits, QueryCap.calls_nil]
  | cons input inputs ih =>
    have hevent : (fun seed => TraceHits (fun query => DerivationHit query seed) (input :: inputs)) =
        fun seed => DerivationHit input seed ∨ TraceHits (fun query => DerivationHit query seed) inputs := by
      funext seed
      simp [TraceHits]
    rw [hevent, QueryCap.calls_cons]
    by_cases hinput : IsDerivationQuery input
    · rw [if_pos hinput, Nat.cast_add, Nat.cast_one, ENNReal.add_div]
      exact (probEvent_or_le _ _ _).trans (add_le_add (probEvent_derivationHit_le input) ih)
    · have hnone : ∀ seed, ¬DerivationHit input seed := fun seed h => hinput ⟨seed, h⟩
      simpa only [hnone, false_or, if_neg hinput, Nat.zero_add] using ih

theorem probOutput_stopBefore_derivation_le {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl
      (QueryCap.counted (hashBad IsDerivationQuery) computation)).run' cache), result.2 ≤ q) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (stopBefore (hashBad (fun input => DerivationHit input seed)) computation)).run' cache] ≤
      q / ((2 ^ 256 : Nat) : ENNReal) := by
  let trace := (simulateQ romImpl (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (TraceHits (fun input => DerivationHit input seed) result.2)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (TraceHits (fun input => DerivationHit input seed) result.2)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hresult
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (probEvent_derivationHitLog_le result.2).trans (ENNReal.div_le_div
        (by exact_mod_cast traceHashes_selected_le IsDerivationQuery computation cache q hbound result hresult) le_rfl)

theorem probEvent_derivation_cache_change_le {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => DerivationHit input seed) (initial seed) cache)
    (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl
      (QueryCap.counted (hashBad IsDerivationQuery) computation)).run' cache), result.2 ≤ q)
    (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed => (simulateQ romImpl computation).run' (initial seed)] ≤
      Pr[event | (simulateQ romImpl computation).run' cache] + q / ((2 ^ 256 : Nat) : ENNReal) := by
  let stopped := fun seed =>
    (simulateQ romImpl (stopBefore (hashBad (fun input => DerivationHit input seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le (fun input => DerivationHit input seed)
          computation (initial seed) cache (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add (le_refl (Pr[event | (simulateQ romImpl computation).run' cache]))
        (probOutput_stopBefore_derivation_le computation cache q hbound)

end SphincsSecurity.Seeded
