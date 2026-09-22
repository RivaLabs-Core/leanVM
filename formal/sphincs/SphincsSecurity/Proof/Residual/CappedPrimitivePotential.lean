import SphincsSecurity.Proof.Residual.CappedMonitoredSource

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  gameInputs initialAllowed initialKnown referenceFamilyWords
  simulateQ adversaryImpl FtsProbeSimulation.unloggedRetainedRestComputation environment lazyRun
set_option backward.isDefEq.respectTransparency false

theorem initialCappedMonitoredSource_interface_primitive_messages (key : SecretKey) (original : Security.Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget monitorBudget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : Security.HasHashQueryBound original budget) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none | initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high monitorBudget required stopAfter stopped] +
      (∑' result, Pr[= result | initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high monitorBudget required stopAfter stopped] *
        (result.2.1.memory.interfaceMessages : ENNReal)) / 2 ^ digestBits ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  let inputs := gameInputs (Seeded.memoAdversary (Security.embed original))
  let words := referenceFamilyWords encoding.selections dummy
  let publicReplies := coordinateGraphLabels (initialKnown words exposed) high
  let source := signingCap (FtsProbeSimulation.unloggedRetainedRestComputation (Seeded.memoAdversary (Security.embed original)) ⟨key.root, key.parameter⟩)
  let initial := initialState inputs words exposed
  let env := environment key.parameter inputs (canonicalEncodingInputs_subset_retainedGameInputs (Seeded.memoAdversary (Security.embed original)) key.parameter)
    words publicReplies encoding.selections encoding.rows
  let computation := simulateQ (adversaryImpl inputs key.parameter key.root words encoding.selections) source
  let native := lazyRun env computation initial
  have herasure : (fun result => (result.1, result.2.1)) <$>
      initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high monitorBudget required stopAfter stopped = native := by
    exact monitoredRun_erasure key inputs (canonicalEncodingInputs_subset_retainedGameInputs (Seeded.memoAdversary (Security.embed original)) key.parameter)
      words publicReplies encoding.selections encoding.rows monitorBudget required stopAfter source
      (initial, initialCertificateMonitor keygenHashCost stopped)
  have hsmall : budget < 2 ^ 256 := hbudget.trans_lt (by norm_num)
  have hnativeCost (result : Option (Option ((Forgery × Bool) × Nat)) × State inputs) (hr : native result ≠ 0) :
      result.2.memory.interfaceHashes ≤ budget := by
    dsimp only [native, computation, source] at hr
    rw [hroot] at hr
    exact lazyInitialCappedSource_interfaceHashes_le key.parameter hparameter inputs
      (canonicalEncodingInputs_subset_retainedGameInputs (Seeded.memoAdversary (Security.embed original)) key.parameter)
      original (sourceInputs_capped_subset_gameInputs (Seeded.memoAdversary (Security.embed original)))
      encoding hencoding dummy exposed high budget hsmall hcost result hr
  have ha : ∀ coordinate, (initial.candidates coordinate).Nonempty := initialAllowed_nonempty words exposed
  have hc : ResidualByteFrontend.RowsCovered inputs (project initial) := initialState_rowsCovered inputs words exposed
  have hin : sourceInputs key source ⊆ inputs := sourceInputs_capped_subset_gameInputs (Seeded.memoAdversary (Security.embed original)) key
  have hd : 2 * budget ≤ 2 ^ digestBits := by
    norm_num only [digestBits]
    omega
  have hpotential := lazyRun_source_interfacePotential inputs words publicReplies encoding.selections encoding.rows key
    (canonicalEncodingInputs_subset_retainedGameInputs (Seeded.memoAdversary (Security.embed original)) key.parameter) source hin initial budget
    (referenceEncodingAuxiliary_select encoding hencoding) ha hc (initialState_hiddenCandidateBound inputs words exposed)
    (ResidualByteFrontend.replyClean_empty _) (InterfaceResources.initial inputs words exposed) hd hnativeCost
  have h := (stop_add_messages_le_expected_interfacePotential budget native).trans
    (hpotential.trans_eq (interfaceLivePotential_initial inputs words exposed budget))
  rw [← herasure, probEvent_map, tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete.RetainedResidual
