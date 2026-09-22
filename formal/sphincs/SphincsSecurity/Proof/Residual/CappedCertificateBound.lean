import SphincsSecurity.Proof.Residual.CappedPrimitivePotential

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem expected_initialCappedMonitoredSource_full_unit_count_le
    (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hq : ∀ result, initialCappedMonitoredSource key adversary encoding dummy exposed high q Finset.univ
      (proposalStop stopAfter) stopped result ≠ 0 → result.2.1.memory.external.hashCalls ≤ q)
    (hbudget : q ≤ 2 ^ 127 + 2 ^ 64) :
    (∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] *
      certificateBankCount result.2.2.bank) ≤
        (2 ^ 128 : ENNReal)⁻¹ *
          (∑' result, Pr[= result | initialCappedMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] *
            result.2.1.memory.messageCalls.length) + (q : ENNReal) * fullCertificateExcessRate := by
  let state : ProposalState (gameInputs adversary) :=
    ([], initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed, initialCertificateMonitor keygenHashCost stopped)
  let law := proposalRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter)
    (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) state
  have hvalid : MonitoredValid (gameInputs adversary) state.2 :=
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
  have hinv : ProposalInvariant key fixedProposalLength state :=
    certificateProposalInvariant_initial key fixedProposalLength keygenHashCost _ stopped (fun _ => le_rfl)
  have hproject : Prod.map id Prod.snd <$> law =
      initialCappedMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped :=
    proposalRun_erasure key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
      (referenceFamilyWords encoding.selections dummy)
      (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
      encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter) _ state
  have herase (weight : Option (Option ((Forgery × Bool) × Nat)) × MonitoredState (gameInputs adversary) → ENNReal) :
      (∑' result, Pr[= result | law] * weight (Prod.map id Prod.snd result)) =
        ∑' result, Pr[= result |
          initialCappedMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] * weight result := by
    have h := congrArg (fun p => ∑' result, Pr[= result | p] * weight result) hproject
    rw [tsum_probOutput_map_mul] at h
    exact h
  have hmass : ∀ result, law result ≠ 0 → result.2.2.2.creationMass ≤ (q : ENNReal) := by
    intro result hresult
    have h := map_nonzero law (Prod.map id Prod.snd) result hresult
    rw [hproject] at h
    exact (initialCappedMonitoredSource_resources key adversary encoding dummy exposed high q Finset.univ
      (proposalStop stopAfter) stopped _ h).2.1.trans (Nat.cast_le.mpr (hq _ h))
  have hcost := expected_proposalRun_creationCost_le_mass_terminalPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ stopAfter fixedProposalLength
    (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) state hvalid
    (sourceInputs_capped_subset_gameInputs adversary key) hbudget hinv
  have huniform := expected_proposalRun_terminalPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter)
    (signingCap (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) state hvalid
    (sourceInputs_capped_subset_gameInputs adversary key) fixedProposalLength
    (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹)
  change (∑' result, Pr[= result | law] * terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength
    (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) result.2.1) = _ at huniform
  have hzero : state.2.2.creationCost = 0 := rfl
  rw [hzero, zero_add] at hcost
  have hempty : state.1 = [] := rfl
  rw [hempty, terminalProposalPotential_empty] at huniform
  calc
    _ ≤ ∑' result, Pr[= result |
        initialCappedMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] * result.2.2.creationCost :=
      expected_initialCappedMonitoredSource_count_le_creationCost key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped
    _ = ∑' result, Pr[= result | law] * result.2.2.2.creationCost := (herase (fun result => result.2.2.creationCost)).symm
    _ ≤ ∑' result, Pr[= result | law] * (result.2.2.2.creationMass *
        terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength (terminalCertificatePrice Finset.univ) result.2.1) := hcost
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (∑' result, Pr[= result | law] * result.2.2.2.creationMass) +
        (q : ENNReal) * ∑' result, Pr[= result | law] * terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength
          (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) result.2.1 :=
      expected_weighted_terminalPotential_le law (fun result => result.2.1) (fun result => result.2.2.2.creationMass)
        q (2 ^ 128 : ENNReal)⁻¹ hmass fixedProposalLength (terminalCertificatePrice Finset.univ)
    _ ≤ _ := by
      rw [huniform]
      have hm := herase (fun result => result.2.2.creationMass)
      dsimp only [Prod.map] at hm
      rw [hm]
      exact add_le_add (mul_le_mul' le_rfl
        (expected_initialCappedMonitoredSource_creationMass_le_messageCalls key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped))
        (mul_le_mul' le_rfl uniformWordAverage_full_price_excess_le)

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec ENNReal CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem expected_messages_le_interface {α : Type} {inputs : Finset HashInput}
    (law : SPMF (α × MonitoredState inputs))
    (hbound : ∀ result, law result ≠ 0 → result.2.1.memory.honestHashes ≤ 2 ^ 64) :
    (∑' result, Pr[= result | law] * (result.2.1.memory.messageCalls.length : ENNReal)) ≤
      (∑' result, Pr[= result | law] * (result.2.1.memory.interfaceMessages : ENNReal)) + 2 ^ 64 := by
  calc
    _ ≤ ∑' result, Pr[= result | law] * ((result.2.1.memory.interfaceMessages : ENNReal) + 2 ^ 64) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : law result = 0
      · simp only [SPMF.probOutput_eq_apply, hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        have hh := (Memory.honestMessages_le_hashes result.2.1.memory).trans (hbound result hr)
        have hm : result.2.1.memory.messageCalls.length ≤ result.2.1.memory.interfaceMessages + 2 ^ 64 := by
          unfold Memory.interfaceMessages
          omega
        exact_mod_cast hm
    _ ≤ _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)

theorem initialCappedMonitoredSource_primitive_add_count_le (key : SecretKey) (original : Security.Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : Security.HasHashQueryBound original q) (hbudget : q ≤ 2 ^ 127) :
    let law := initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high
      (q + 2 ^ 64) Finset.univ (proposalStop stopAfter) stopped
    Pr[fun result => result.1 = none | law] +
      (∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank) ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2) +
        ((q + 2 ^ 64 : Nat) : ENNReal) * fullCertificateExcessRate + (2 ^ 64 : ENNReal) / 2 ^ 128 := by
  dsimp only
  let law := initialCappedMonitoredSource key (Seeded.memoAdversary (Security.embed original)) encoding dummy exposed high
    (q + 2 ^ 64) Finset.univ (proposalStop stopAfter) stopped
  let externalMessages : ENNReal := ∑' result, Pr[= result | law] * (result.2.1.memory.interfaceMessages : ENNReal)
  let allMessages : ENNReal := ∑' result, Pr[= result | law] * (result.2.1.memory.messageCalls.length : ENNReal)
  have hs : q < 2 ^ 256 := hbudget.trans_lt (by norm_num)
  have hp := initialCappedMonitoredSource_interface_primitive_messages key original encoding dummy exposed high q (q + 2 ^ 64)
    Finset.univ (proposalStop stopAfter) stopped hparameter hencoding hroot hcost hbudget
  have hc := expected_initialCappedMonitoredSource_full_unit_count_le key (Seeded.memoAdversary (Security.embed original))
    encoding dummy exposed high (q + 2 ^ 64) stopAfter stopped
    (initialCappedMonitoredSource_hashCalls key original encoding dummy exposed high (q + 2 ^ 64) Finset.univ
      (proposalStop stopAfter) stopped q hparameter hencoding hroot hs hcost)
    (Nat.add_le_add_right hbudget _)
  have hm : allMessages ≤ externalMessages + 2 ^ 64 := expected_messages_le_interface law
    (initialCappedMonitoredSource_honestHashes key original encoding dummy exposed high (q + 2 ^ 64) Finset.univ
      (proposalStop stopAfter) stopped)
  have hc' : (∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank) ≤
      externalMessages / 2 ^ 128 + ((q + 2 ^ 64 : Nat) : ENNReal) * fullCertificateExcessRate + (2 ^ 64 : ENNReal) / 2 ^ 128 := by
    apply hc.trans
    calc
      _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (externalMessages + 2 ^ 64) +
          ((q + 2 ^ 64 : Nat) : ENNReal) * fullCertificateExcessRate := add_le_add (mul_le_mul' le_rfl hm) le_rfl
      _ = _ := by simp only [div_eq_mul_inv]; ring
  apply (add_le_add le_rfl hc').trans
  rw [← add_assoc, ← add_assoc]
  exact add_le_add (add_le_add hp le_rfl) le_rfl

end SphincsSecurity.Concrete.RetainedResidual
