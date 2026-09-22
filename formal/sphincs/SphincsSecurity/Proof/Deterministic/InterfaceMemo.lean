import SphincsSecurity.Proof.Deterministic.MemoGame
import SphincsSecurity.Proof.Deterministic.InterfaceGameComparison
import SphincsSecurity.Proof.Deterministic.RequestSampling

open OracleComp OracleSpec

namespace DeterministicSigning

set_option backward.isDefEq.respectTransparency false
variable {ι : Type} {base : OracleSpec ι} {Request Answer : Type}

theorem FreshRequests.counted {α : Type} {used : Set Request}
    {computation : OracleComp (base + (Request →ₒ Answer)) α} (h : FreshRequests used computation)
    (selected : (base + (Request →ₒ Answer)).Domain → Prop) [DecidablePred selected] :
    FreshRequests used (SphincsSecurity.QueryCap.counted selected computation) := by
  induction h with
  | pure value => exact .pure _
  | base input next _ ih =>
    rw [SphincsSecurity.QueryCap.counted_query_bind]
    exact .base input _ (fun answer => by simpa only [bind_pure_comp] using (ih answer).map _)
  | request input hnew next _ ih =>
    rw [SphincsSecurity.QueryCap.counted_query_bind]
    exact .request input hnew _ (fun answer => by simpa only [bind_pure_comp] using (ih answer).map _)

theorem memoize_counted {α : Type} [DecidableEq Request]
    (selected : (base + (Request →ₒ Answer)).Domain → Prop) [DecidablePred selected]
    (hfree : ∀ request, ¬selected (.inr request))
    (computation : OracleComp (base + (Request →ₒ Answer)) α) (cache : QueryCache (Request →ₒ Answer)) :
    memoize (SphincsSecurity.QueryCap.counted selected computation) cache =
      SphincsSecurity.QueryCap.counted selected (memoize computation cache) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
    cases input with
    | inl input =>
      simp only [SphincsSecurity.QueryCap.counted_query_bind, memoize_base, bind_pure_comp, memoize_map, ih]
    | inr request =>
      simp only [SphincsSecurity.QueryCap.counted_query_bind, memoize_request, bind_pure_comp, memoize_map]
      cases hc : cache request with
      | some answer => simp only [ih, if_neg (hfree request), Nat.zero_add, Prod.mk.eta, id_map']
      | none => simp only [SphincsSecurity.QueryCap.counted_query_bind, ih, bind_pure_comp]

end DeterministicSigning

namespace SphincsSecurity.Seeded

open DeterministicSigning Concrete.FtsProbeSimulation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Security.experiment sourceGame transcriptReduction

theorem withRequestLog_eq_signingTrace {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    withRequestLog computation = signingTraceComputation computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    change withRequestLog (liftM ((OracleWorld + SigningSpec).query input) >>= next) = (do
      let answer ← liftM ((OracleWorld + SigningSpec).query input)
      let result ← signingTraceComputation (next answer)
      pure (result.1, signingLogFragment input answer ++ result.2))
    cases input with
    | inl world => simp only [withRequestLog_base, signingLogFragment, List.nil_append,
        Prod.mk.eta, bind_pure, ih]
    | inr message => simp only [withRequestLog_request, signingLogFragment,
        List.singleton_append, bind_pure_comp, ih]

theorem sourceGame_eq_traced (publicKey : PublicKey) (adversary : Adversary) :
    sourceGame publicKey adversary = tracedGameRestComputation adversary publicKey := by
  rw [sourceGame, withRequestLog_eq_signingTrace, tracedGameRestComputation]
  apply bind_congr
  rintro ⟨forgery, log⟩
  simp only [finishGame, baseLift_eq_liftM, liftM_bind, liftM_pure, transcriptWin, liftOracleWorldLeft]
  rfl

theorem evaluateSource_counted_memo_budget (sign : Message → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support (evaluateSource sign (QueryCap.counted Security.IsAdversaryHash
      (sourceGame publicKey adversary)) cache), result.2 ≤ q) :
    ∀ result ∈ support (evaluateSource sign (QueryCap.counted Security.IsAdversaryHash
      (sourceGame publicKey (memoAdversary adversary))) cache), result.2 ≤ q := by
  have heq := evalDist_runSigning_memoize sign (QueryCap.counted Security.IsAdversaryHash (sourceGame publicKey adversary)) cache
  rw [memoize_counted Security.IsAdversaryHash (by intro request; simp [Security.IsAdversaryHash]),
    ← fst_transcriptReduction, QueryCap.counted_map] at heq
  have hfirst : ∀ result ∈ support (evaluateSource sign
      (QueryCap.counted Security.IsAdversaryHash (transcriptReduction publicKey adversary)) cache), result.2 ≤ q := by
    intro result hresult
    apply hbound (result.1.1, result.2)
    rw [evaluateSource, mem_support_iff_of_evalDist_eq heq, ← evaluateSource, evaluateSource_map, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [← snd_transcriptReduction, QueryCap.counted_map, evaluateSource_map]
  intro result hresult
  rw [support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact hfirst record hrecord

end SphincsSecurity.Seeded
