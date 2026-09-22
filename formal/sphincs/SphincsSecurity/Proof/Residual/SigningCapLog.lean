import SphincsSecurity.Proof.Residual.SigningCap
import SphincsSecurity.Proof.Fts.StoppedSigningLog

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec FtsProbeSimulation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem signingCap_withSigningLog {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec) (cap : Nat) :
    (fun result : Option (α × Nat) × QueryLog SigningSpec =>
      result.1.map (fun value => ((value.1, result.2), value.2))) <$>
        withSigningLog (QueryCap.run IsSigningRequest computation cap) log =
      QueryCap.run IsSigningRequest (withSigningLog computation log) cap := by
  induction computation using OracleComp.inductionOn generalizing cap log with
  | pure value => simp only [QueryCap.run_pure, withSigningLog_pure, map_pure, Option.map_some]
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind, withSigningLog_query_bind, QueryCap.run_query_bind]
      by_cases hs : IsSigningRequest input
      · rw [if_pos hs, if_pos hs]
        cases cap with
        | zero => simp only [withSigningLog_pure, map_pure, Option.map_none]
        | succ cap =>
            rw [withSigningLog_query_bind, map_bind]
            exact bind_congr (fun answer => ih answer _ cap)
      · rw [if_neg hs, if_neg hs, withSigningLog_query_bind, map_bind]
        exact bind_congr (fun answer => ih answer _ cap)

theorem counted_signingLog_length {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (log : QueryLog SigningSpec)
    (result : (α × QueryLog SigningSpec) × Nat)
    (hr : result ∈ support (QueryCap.counted IsSigningRequest (withSigningLog computation log))) :
    result.1.2.length = log.length + result.2 := by
  induction computation using OracleComp.inductionOn generalizing log result with
  | pure value =>
      simp only [withSigningLog_pure, QueryCap.counted_pure, mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [withSigningLog_query_bind, QueryCap.counted_query_bind] at hr
      simp only [mem_support_bind_iff, mem_support_query, true_and, mem_support_pure_iff] at hr
      obtain ⟨answer, tail, htail, heq⟩ := hr
      subst result
      have h := ih answer _ tail htail
      have hlen : (signingLogFragment input answer).length = if IsSigningRequest input then 1 else 0 := by
        cases input <;> simp [signingLogFragment, IsSigningRequest]
      simp only [List.length_append, hlen] at h
      exact h.trans (Nat.add_assoc _ _ _)

private theorem pmf_simulate_support {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec PMF) (computation : OracleComp spec α) :
    (simulateQ impl computation).support ⊆ support computation := by
  intro result hr
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, mem_support_pure_iff] using hr
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨answer, _, htail⟩ := hr
      exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query _ _, ih answer htail⟩

theorem signingCap_preserves_valid_event {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) PMF)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (event : α → QueryLog SigningSpec → Prop)
    (hvalid : ∀ value log, event value log → log.length ≤ signatureLimit) :
    Pr[fun result => event result.1 result.2 | simulateQ impl (withSigningLog computation [])] =
      Pr[fun result => result.1.elim False (fun value => event value.1 result.2) |
        simulateQ impl (withSigningLog (signingCap computation) [])] := by
  have hleft := congrArg (simulateQ impl) (QueryCap.counted_forget IsSigningRequest (withSigningLog computation []))
  rw [simulateQ_map] at hleft
  rw [← hleft, probEvent_map]
  have hright : Pr[fun result => result.elim False (fun value => event value.1.1 value.1.2) |
      simulateQ impl (QueryCap.run IsSigningRequest (withSigningLog computation []) signatureLimit)] =
      Pr[fun result => result.1.elim False (fun value => event value.1 result.2) |
        simulateQ impl (withSigningLog (signingCap computation) [])] := by
    rw [← congrArg (simulateQ impl) (signingCap_withSigningLog computation [] signatureLimit),
      simulateQ_map, probEvent_map]
    apply congrArg (probEvent _)
    funext result
    rcases result with ⟨value, log⟩
    cases value <;> rfl
  rw [← hright, QueryCap.run_eq_counted, ← PMF.monad_map_eq_map, probEvent_map]
  have hiff : ∀ result ∈ (simulateQ impl
      (QueryCap.counted IsSigningRequest (withSigningLog computation []))).support,
      event result.1.1 result.1.2 ↔
        (QueryCap.finish signatureLimit result).elim False (fun value => event value.1.1 value.1.2) := by
    intro result hr
    have hlen := counted_signingLog_length computation [] result (pmf_simulate_support impl _ hr)
    simp only [List.length_nil, Nat.zero_add] at hlen
    unfold QueryCap.finish
    split
    · rfl
    · simp only [Option.elim_none, iff_false]
      intro hevent
      exact ‹¬result.2 ≤ signatureLimit› (hlen ▸ hvalid _ _ hevent)
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases hr : simulateQ impl (QueryCap.counted IsSigningRequest (withSigningLog computation [])) result = 0
  · simp only [PMF.probOutput_eq_apply, hr, ite_self]
  · have hi := hiff result ((PMF.mem_support_iff _ _).mpr hr)
    dsimp only [Function.comp_def]
    split_ifs <;> tauto

theorem signingCap_preserves_valid_event_probComp {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) ProbComp)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (event : α → QueryLog SigningSpec → Prop)
    (hvalid : ∀ value log, event value log → log.length ≤ signatureLimit) :
    Pr[fun result => event result.1 result.2 | simulateQ impl (withSigningLog computation [])] =
      Pr[fun result => result.1.elim False (fun value => event value.1 result.2) |
        simulateQ impl (withSigningLog (signingCap computation) [])] := by
  have h := signingCap_preserves_valid_event (impl.liftTarget PMF) computation event hvalid
  simp only [simulateQ_liftTarget] at h
  exact h

end SphincsSecurity.Concrete.RetainedResidual
