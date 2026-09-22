import SphincsSecurity.Proof.Fts.RegisteredCertificatePrice

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def registeredPrefixStop : RegisteredCertificateStop :=
  fun input state length record => decide (
    targetProposalOverhead * (state.1.1.2 ++ signingLogFragment input record.output).length + (proposalPrefixSlack : ENNReal) <
      ((state.2.proposals + length : Nat) : ENNReal))

def initialRegisteredCertificateLedger (q : Nat) : RegisteredCertificateLedger where
  hashes := q
  signatures := signatureLimit
  bank := fun _ => false
  stopped := false
  proposals := 0
  messages := 0

def RegisteredCertificateInvariant (key : SecretKey) (q total : Nat)
    (state : List Index × RegisteredCertificateLedgerState) : Prop :=
  state.2.2.stopped = false → RegisteredCertificateBounds key q total state

theorem registeredCertificateInvariant_initial (key : SecretKey) (q total : Nat) (cache : QueryCache HashSpec)
    (hpool : fixedProposalLength ≤ total) :
    RegisteredCertificateInvariant key q total ([], ((cache, []), ∅), initialRegisteredCertificateLedger q) := by
  intro _
  refine ⟨by simp [initialRegisteredCertificateLedger], rfl, by simp [initialRegisteredCertificateLedger], ?_, ?_, hpool⟩
  · intro index
    simp [observedOptionalSigningViews, signingSlotsAtIndex]
  · simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add]
    exact zero_le

theorem originalProposalRecord_registered_support (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : RegisteredTargetState) (record : ProposalExecutionRecord input)
    (hrecord : record ∈ (originalProposalRecord key input state.1.1).support) :
    (record.output, registeredRecordNext input state record) ∈ support ((registeredTargetImpl key input).run state) := by
  have h := (PMF.mem_support_map_iff (fun record => (record.output, registeredRecordNext input state record)) _ _).mpr
    ⟨record, hrecord, rfl⟩
  rw [originalProposalRecord_registered, probCompLift_support] at h
  exact h

theorem registeredCertificateInvariant_advance (key : SecretKey) (q total : Nat)
    (required : Finset FtsTree) (stopAfter : RegisteredCertificateStop)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × RegisteredCertificateLedgerState)
    (suffix : List Index) (length : Nat) (record : ProposalExecutionRecord input)
    (hrecord : record ∈ (originalProposalRecord key input state.2.1.1.1).support)
    (hinv : RegisteredCertificateInvariant key q total state)
    (hactive : RegisteredCertificateActive key input state.2) (hlength : length = suffix.length)
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter record.cache)
        key.root (state.2.1.1.2 ++ signingLogFragment input record.output)) index).card ≤ (state.1 ++ suffix).count index) :
    RegisteredCertificateInvariant key q total (state.1 ++ suffix, registeredProposalAdvance
      (registeredLedgerUpdate key required
        (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record))
      input state.2 length record) := by
  intro hpost
  have hbefore := hinv hactive.1
  have hstop : registeredPrefixStop input state.2 length record = false := by
    simp only [registeredProposalAdvance, registeredLedgerUpdate, if_pos hactive, Bool.or_eq_false_iff] at hpost
    exact hpost.1
  have hprefix : ((state.2.2.proposals + length : Nat) : ENNReal) ≤
      targetProposalOverhead * (state.2.1.1.2 ++ signingLogFragment input record.output).length + (proposalPrefixSlack : ENNReal) := by
    simp only [registeredPrefixStop, decide_eq_false_iff_not] at hstop
    exact le_of_not_gt hstop
  have hs := originalProposalRecord_registered_support key input state.2.1 record hrecord
  have hcard := registeredTargetImpl_card_le key input state.2.1 _ hs
  have hlog := registeredTargetImpl_log_length key input state.2.1 _ hs
  constructor
  · change (registeredRecordNext input state.2.1 record).2.card +
      (registeredLedgerUpdate key required _ input state.2 length record).hashes ≤ q
    rw [registeredLedgerUpdate, if_pos hactive]
    have hcost := hactive.2.2.2.1
    have hqueries := hbefore.queries_le
    change (registeredRecordNext input state.2.1 record).2.card ≤ state.2.1.2.card + adversaryHashCost input at hcard
    dsimp only
    omega
  · simp only [registeredProposalAdvance, registeredLedgerUpdate, if_pos hactive, List.length_append,
      hbefore.proposals_eq, hlength]
  · change (registeredLedgerUpdate key required _ input state.2 length record).signatures +
      (registeredRecordNext input state.2.1 record).1.2.length = signatureLimit
    rw [registeredLedgerUpdate, if_pos hactive, hlog]
    have hcost := hactive.2.2.2.2
    have hsignature := hbefore.signatures_eq
    dsimp only
    omega
  · exact hcounts
  · simpa only [registeredProposalAdvance, registeredLedgerUpdate, if_pos hactive, registeredRecordNext,
      List.length_append, hbefore.proposals_eq, hlength] using hprefix
  · exact hbefore.total_le

theorem registeredLedgerImpl_sign_run (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (message : Message) (state : List Index × RegisteredCertificateLedgerState) :
    (registeredLedgerImpl key required stopAfter (.inr message)).run state =
      if RegisteredCertificateActive key (.inr message) state.2 then
        (recordProposalBridge (originalProposalRecord key (.inr message) state.2.1.1.1)
          (registeredRejectedProposal key (.inr message) state.2)
          targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le).map
            (fun result => (result.2.output, state.1 ++ result.1 ++ [result.2.index],
              registeredProposalAdvance (registeredLedgerUpdate key required stopAfter)
                (.inr message) state.2 (result.1.length + 1) result.2))
      else (originalProposalRecord key (.inr message) state.2.1.1.1).map (fun record =>
        (record.output, state.1, registeredProposalAdvance (registeredLedgerUpdate key required stopAfter) (.inr message) state.2 0 record)) := by
  have hactive : registeredProposalActive key (registeredCertificateEnabled key) (.inr message) state.2 =
      decide (RegisteredCertificateActive key (.inr message) state.2) := by
    by_cases h : RegisteredCertificateActive key (.inr message) state.2
    · simp [registeredProposalActive, registeredCertificateEnabled, h, h.2.1]
    · simp [registeredProposalActive, registeredCertificateEnabled, h]
  simp only [registeredLedgerImpl, registeredProposalImpl, proposalRecordImpl, StateT.run_mk, hactive, decide_eq_true_eq]

theorem registeredLedgerImpl_invariant (key : SecretKey) (q total : Nat)
    (required : Finset FtsTree) (stopAfter : RegisteredCertificateStop)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × RegisteredCertificateLedgerState)
    (hinv : RegisteredCertificateInvariant key q total state)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × RegisteredCertificateLedgerState))
    (hr : result ∈ ((registeredLedgerImpl key required
      (fun input state length record => registeredPrefixStop input state length record || stopAfter input state length record)
      input).run state).support) : RegisteredCertificateInvariant key q total result.2 := by
  cases input with
  | inl world =>
    simp only [registeredLedgerImpl, registeredProposalImpl, proposalRecordImpl, registeredProposalActive,
      StateT.run_mk, Bool.false_eq_true, if_false, PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    by_cases hactive : RegisteredCertificateActive key (.inl world) state.2
    · have hbefore := hinv hactive.1
      have hafter := registeredCertificateInvariant_advance key q total required stopAfter (.inl world)
        state [] 0 record hrecord hinv hactive rfl (fun index => by
          have hc := originalProposalRecord_slots_le key (.inl world) state.2.1.1 hactive.2.2.1 record hrecord index
          change _ ≤ _ + 0 at hc
          rw [Nat.add_zero] at hc
          simpa only [List.append_nil] using hc.trans (hbefore.counts_le index))
      simpa only [List.append_nil] using hafter
    · intro hpost
      simp only [registeredProposalAdvance, registeredLedgerUpdate, if_neg hactive, Bool.true_eq_false] at hpost
  | inr message =>
    rw [registeredLedgerImpl_sign_run] at hr
    by_cases hactive : RegisteredCertificateActive key (.inr message) state.2
    · rw [if_pos hactive, PMF.mem_support_map_iff] at hr
      obtain ⟨source, hsource, rfl⟩ := hr
      have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
      rw [recordProposalBridge_record] at hrecord
      have hbefore := hinv hactive.1
      have hafter := registeredCertificateInvariant_advance key q total required stopAfter (.inr message)
        state (source.1 ++ [source.2.index]) (source.1.length + 1) source.2 hrecord hinv hactive
        (by simp only [List.length_append, List.length_singleton]) (fun index => by
          have hc := originalProposalRecord_slots_le key (.inr message) state.2.1.1 hactive.2.2.1 source.2 hrecord index
          change _ ≤ _ + if source.2.index = index then 1 else 0 at hc
          calc
            _ ≤ _ := hc
            _ ≤ state.1.count index + if source.2.index = index then 1 else 0 :=
              Nat.add_le_add_right (hbefore.counts_le index) _
            _ ≤ (state.1 ++ (source.1 ++ [source.2.index])).count index := by
              simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
              split_ifs <;> omega)
      simpa only [List.append_assoc] using hafter
    · rw [if_neg hactive, PMF.mem_support_map_iff] at hr
      obtain ⟨record, _, rfl⟩ := hr
      intro hpost
      simp only [registeredProposalAdvance, registeredLedgerUpdate, if_neg hactive, Bool.true_eq_false] at hpost

end SphincsSecurity.Concrete
