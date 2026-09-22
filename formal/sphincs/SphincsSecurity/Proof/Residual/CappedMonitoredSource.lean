import SphincsSecurity.Proof.Residual.CappedInitialBudget

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] gameInputs initialAllowed initialKnown referenceFamilyWords
  sourceInputs hashInputs canonicalEncodingInputs canonicalGraphInputs

theorem sourceInputs_capped_subset_gameInputs (adversary : Adversary) (key : SecretKey) :
    sourceInputs key (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) ⊆ gameInputs adversary :=
  (sourceInputs_queryCap_subset key IsSigningRequest _ signatureLimit).trans
    (sourceInputs_unlogged_subset_gameInputs adversary key)

variable (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
  (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
  (q : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)

noncomputable def initialCappedMonitoredSource : SPMF (Option (Option ((Forgery × Bool) × Nat)) × MonitoredState (gameInputs adversary)) :=
  monitoredRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter
    (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost stopped)

theorem initialCappedMonitoredSource_resources
    (result : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState (gameInputs adversary))
    (hresult : initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0) :
    MonitorResources result.2.2 result.2.1.memory :=
  monitoredRun_resources key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter
    (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost stopped)
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_capped_subset_gameInputs adversary key) ⟨le_rfl, bot_le, Nat.zero_le _⟩ result hresult

theorem expected_initialCappedMonitoredSource_count_le_creationCost :
    (∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      certificateBankCount result.2.2.bank) ≤
    ∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      result.2.2.creationCost :=
  expected_monitoredRun_count_le_creationCost key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed) keygenHashCost stopped
    (initialAllowed_nonempty _ exposed) (initialState_rowsCovered _ _ exposed)
    (sourceInputs_capped_subset_gameInputs adversary key) (fun _ _ => rfl)

theorem expected_initialCappedMonitoredSource_creationMass_le_messageCalls :
    (∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      result.2.2.creationMass) ≤
    ∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      result.2.1.memory.messageCalls.length := by
  have hpayment := expected_monitoredRun_creationMass_le_messageCalls key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed) keygenHashCost stopped
    (initialAllowed_nonempty _ exposed) (initialState_rowsCovered _ _ exposed)
    (sourceInputs_capped_subset_gameInputs adversary key)
  apply hpayment.trans
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] = 0
  · change Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] * _ ≤ _
    simp only [hr, zero_mul, le_refl]
  · rw [SPMF.probOutput_eq_apply] at hr
    exact mul_le_mul' le_rfl (Nat.cast_le.mpr
      (initialCappedMonitoredSource_resources key adversary encoding dummy exposed high q required stopAfter stopped result hr).2.2)

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] gameInputs initialAllowed initialKnown referenceFamilyWords
  sourceInputs hashInputs canonicalEncodingInputs canonicalGraphInputs

variable (key : SecretKey) (original : Security.Adversary) (encoding : ReferenceEncodingAuxiliary)
  (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
  (high : CanonicalGraphHighHalves) (budget : Nat) (required : Finset FtsTree)
  (stopAfter : CertificateStopRule) (stopped : Bool)

theorem initialCappedMonitoredSource_honestHashes
    (result : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState (gameInputs (Seeded.memoAdversary (Security.embed original))))
    (hr : initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high
      budget required stopAfter stopped result ≠ 0) : result.2.1.memory.honestHashes ≤ 2 ^ 64 := by
  unfold initialCappedMonitoredSource at hr
  have hnative := map_nonzero _ (fun result => (result.1, result.2.1)) result hr
  rw [monitoredRun_erasure] at hnative
  exact lazyRun_signingCap_honestHashes key _ _ _ _ _ _ _
    (sourceInputs_unlogged_subset_gameInputs _ key) exposed (result.1, result.2.1) hnative

theorem initialCappedMonitoredSource_interfaceHashes
    (q : Nat) (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hsmall : q < 2 ^ 256) (hq : Security.HasHashQueryBound original q)
    (result : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState (gameInputs (Seeded.memoAdversary (Security.embed original))))
    (hr : initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high
      budget required stopAfter stopped result ≠ 0) : result.2.1.memory.interfaceHashes ≤ q := by
  unfold initialCappedMonitoredSource at hr
  have hnative := map_nonzero _ (fun result => (result.1, result.2.1)) result hr
  rw [monitoredRun_erasure, hroot] at hnative
  exact lazyInitialCappedSource_interfaceHashes_le key.parameter hparameter _ _ original
    (sourceInputs_capped_subset_gameInputs _) encoding hencoding dummy exposed high q hsmall hq (result.1, result.2.1) hnative

theorem initialCappedMonitoredSource_hashCalls
    (q : Nat) (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hsmall : q < 2 ^ 256) (hq : Security.HasHashQueryBound original q)
    (result : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState (gameInputs (Seeded.memoAdversary (Security.embed original))))
    (hr : initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high
      budget required stopAfter stopped result ≠ 0) : result.2.1.memory.external.hashCalls ≤ q + 2 ^ 64 := by
  have hh := initialCappedMonitoredSource_honestHashes key original encoding dummy exposed high budget required stopAfter stopped result hr
  have hi := initialCappedMonitoredSource_interfaceHashes key original encoding dummy exposed high budget required stopAfter stopped
    q hparameter hencoding hroot hsmall hq result hr
  unfold Memory.interfaceHashes at hi
  omega

theorem Memory.honestMessages_le_hashes (memory : Memory) : memory.honestMessages ≤ memory.honestHashes := by
  unfold Memory.honestMessages Memory.honestHashes
  apply le_trans ?_ (Nat.le_add_left _ _)
  have h (records : List (Message × InterleavedResidual.SigningRecord)) :
      (records.map (fun record => record.2.2.messageCalls.length)).sum ≤
        (records.map (fun record => record.2.2.hashCalls)).sum := by
    induction records with
    | nil => exact le_rfl
    | cons record records ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (List.length_filterMap_le _ _) ih
  exact h memory.records

end SphincsSecurity.Concrete.RetainedResidual
