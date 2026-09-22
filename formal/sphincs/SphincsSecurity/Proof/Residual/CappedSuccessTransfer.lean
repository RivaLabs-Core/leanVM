import SphincsSecurity.Proof.Residual.SigningCapLog
import SphincsSecurity.Proof.Residual.RetainedResidualSuccessTransfer

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting FtsProbeSimulation
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

def cappedVerdict (result : Option ((Forgery × Bool) × Nat)) (log : QueryLog SigningSpec) : Prop :=
  result.elim False (fun value => sourceVerdict value.1 log = true)

theorem prob_gameRest_le_capped_stopped {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary) (memory : Memory) (hlog : memory.log = []) :
    Pr[fun verdict => verdict = true |
      simulateQ (fixedHashWorld context.oracle)
        (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)] ≤
      Pr[StoppedOr cappedVerdict | fixedSourceRun context
        (signingCap (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)) memory] := by
  rw [fixedOriginal_gameRest, probEvent_map]
  have hcap := signingCap_preserves_valid_event_probComp
    ((fixedHashWorld context.oracle) ∘ₛ (expandedAdversaryImpl context.key))
    (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
    (fun value log => sourceVerdict value log = true) (by
      intro value log h
      simp only [sourceVerdict, Bool.and_eq_true, decide_eq_true_eq, SigningTranscript.Valid] at h
      exact h.1.1)
  simp only [QueryImpl.simulateQ_compose] at hcap
  simp only [Function.comp_def]
  rw [hcap]
  have h := prob_originalSource_le_stopped context
    (signingCap (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)) memory cappedVerdict
  rw [hlog] at h
  exact h

theorem prob_gameRest_le_capped_observed {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary)
    (hinputs : sourceInputs context.key
      (signingCap (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (hlog : state.memory.log = []) :
    Pr[fun verdict => verdict = true |
      simulateQ (fixedHashWorld context.oracle)
        (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)] ≤
      Pr[fun result => StoppedOr cappedVerdict (forgetState result) |
        observedRun context.environment context.actual context.auxiliary.seed
          (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
            (signingCap (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩))) state] := by
  have h := prob_gameRest_le_capped_stopped context adversary state.memory hlog
  rw [← observedRun_source_memory context _ hinputs state hcovered hcompatible, probEvent_map] at h
  exact h

end SphincsSecurity.Concrete.RetainedResidual
