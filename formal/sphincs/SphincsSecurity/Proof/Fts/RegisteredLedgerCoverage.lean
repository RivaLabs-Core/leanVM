import SphincsSecurity.Proof.Fts.RegisteredLedgerStops
import SphincsSecurity.Proof.Fts.RegisteredCertificateExpectation

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_registeredCacheLedgerImpl_original {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (stopAfter : RegisteredCertificateStop) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : RegisteredCacheLedgerState) :
    (fun result => (result.1, result.2.1.2.1)) <$>
      (simulateQ (registeredCacheLedgerImpl key required stopAfter) computation).run state =
      (liftM ((simulateQ (registeredTargetImpl key) computation).run state.1.2.1) : PMF _) := by
  have h := congrArg (Functor.map (fun result => (result.1, result.2.2.1)))
    (simulateQ_registeredCacheLedgerImpl_forget key required stopAfter computation state)
  rw [Functor.map_map, registeredLedgerImpl, simulateQ_registeredProposalImpl_original] at h
  exact h

theorem registeredCacheExceptional_initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none) :
    ¬RegisteredCacheExceptional key ((cache, []), ∅) := by
  intro hbad
  have hinvariant := RegisteredCacheInvariant.initial key cache hfinite hmessage
  have h := registeredCacheExceptionWeight_bad key _ hinvariant.2.1 hinvariant.2.2.1 hinvariant.2.2.2 hbad
  have hzero : certificateCacheExceptionWeight key (registeredCache ((cache, []), ∅)) = 0 := by
    apply certificateCacheExceptionWeight_initial
    intro input _
    simp [registeredCache]
  norm_num [hzero] at h

theorem registeredSecurityLedgerRun_live_or_exception {α : Type} (key : SecretKey) (required : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q)
    (result : α × RegisteredCacheLedgerState)
    (hresult : result ∈ ((simulateQ (registeredSecurityLedgerImpl key required) computation).run
      (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)).support)
    (hvalid : result.2.1.2.1.1.2.length ≤ signatureLimit) :
    result.2.1.2.2.stopped = false ∨ RegisteredLedgerPrefixExceptional result.2.1.2 ∨ result.2.2 = true := by
  let initial : RegisteredCacheLedgerState := (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)
  have hforget : (fun r => (r.1.1, r.2)) <$>
      (simulateQ (registeredSecurityLedgerImpl key required)
        (QueryCap.counted Security.IsAdversaryHash computation)).run initial =
      (simulateQ (registeredSecurityLedgerImpl key required) computation).run initial := by
    rw [← StateT.run_map, ← simulateQ_map, QueryCap.counted_forget]
  rw [← hforget, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hresult
  obtain ⟨counted, hcounted, rfl⟩ := hresult
  have hbase : (counted.1, counted.2.1.2.1) ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)) := by
    rw [← probCompLift_support, ← simulateQ_registeredCacheLedgerImpl_original key required _ _ initial,
      PMF.monad_map_eq_map, PMF.mem_support_map_iff]
    exact ⟨counted, hcounted, rfl⟩
  exact registeredSecurityLedgerRun_stop_cases key required q fixedProposalLength hq computation initial rfl
    (RegisteredCacheInvariant.initial key cache hfinite hmessage)
    (by simp [initial, SigningDigestsCached]) (registeredCacheExceptional_initial key cache hfinite hmessage)
    (registeredCertificateInvariant_initial key q fixedProposalLength cache le_rfl)
    counted hcounted (hbound _ hbase) hvalid


theorem registeredCertificate_probability_le_message_excess {α : Type} (key : SecretKey)
    (required : Finset FtsTree) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (q : Nat) (hq : q ≤ (2 ^ 127 + 2 ^ 64)) (hfinite : Finite cache)
    (hmessage : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none)
    (hbound : ∀ result ∈ support ((simulateQ (registeredTargetImpl key)
      (QueryCap.counted Security.IsAdversaryHash computation)).run ((cache, []), ∅)), result.1.2 ≤ q)
    (baseline : ENNReal) (hbaseline : baseline ≠ ⊤) :
    Pr[fun result => result.2.1.2.length ≤ signatureLimit ∧
      ∃ input ∈ result.2.2, TargetCertificateAt key required result.2.1 input |
      (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] ≤
      baseline * (∑' result, Pr[= result | (simulateQ (registeredSecurityLedgerImpl key required) computation).run
        (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)] * result.2.1.2.2.messages) +
      (q : ENNReal) * uniformWordAverage fixedProposalLength (fun word => terminalCertificatePrice required word - baseline) +
      proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q := by
  let stopAfter : RegisteredCertificateStop := fun input state length record =>
    registeredPrefixStop input state length record || registeredCacheStop key input state length record
  let initial : RegisteredCacheLedgerState := (([], ((cache, []), ∅), initialRegisteredCertificateLedger q), false)
  let law := (simulateQ (registeredSecurityLedgerImpl key required) computation).run initial
  let ledgerLaw := (simulateQ (registeredLedgerImpl key required stopAfter) computation).run initial.1
  have hforget := simulateQ_registeredCacheLedgerImpl_forget key required stopAfter computation initial
  have hbank : Pr[fun result => ∃ input, result.2.1.2.2.bank input = true | law] ≤
      baseline * (∑' result, Pr[= result | law] * result.2.1.2.2.messages) +
      (q : ENNReal) * uniformWordAverage fixedProposalLength (fun word => terminalCertificatePrice required word - baseline) := by
    have hcount := expected_registeredCertificate_count_le_message_excess key computation cache q fixedProposalLength required
      (registeredCacheStop key) hq le_rfl baseline hbaseline
    have hbankMap := congrArg (fun dist => ∑' result, Pr[= result | dist] * certificateBankCount result.2.2.2.bank) hforget
    have hmessageMap := congrArg (fun dist => ∑' result, Pr[= result | dist] * (result.2.2.2.messages : ENNReal)) hforget
    rw [tsum_probOutput_map_mul] at hbankMap hmessageMap
    change (∑' result, Pr[= result | ledgerLaw] * certificateBankCount result.2.2.2.bank) ≤
      baseline * (∑' result, Pr[= result | ledgerLaw] * result.2.2.2.messages) + _ at hcount
    rw [← hbankMap, ← hmessageMap] at hcount
    apply le_trans _ hcount
    apply probEvent_le_tsum_probOutput_mul_cost
    rintro result ⟨input, hinput⟩
    exact one_le_certificateBankCount _ input hinput
  have hprefix : Pr[fun result => RegisteredLedgerPrefixExceptional result.2.1.2 | law] ≤ proposalPrefixExceptionBound := by
    have h := congrArg (fun dist => Pr[fun result => RegisteredLedgerPrefixExceptional result.2.2 | dist]) hforget
    rw [probEvent_map] at h
    exact h.le.trans (registeredLedgerRun_prefix_probability_le key required stopAfter computation cache q)
  have hcache : Pr[fun result => result.2.2 = true | law] ≤ 4 * certificateCacheExceptionRate * q :=
    registeredCacheLedger_probability_le key required stopAfter computation cache q hfinite hmessage hbound
  have hproject := congrArg (fun dist => Pr[fun result => result.2.1.2.length ≤ signatureLimit ∧
    ∃ input ∈ result.2.2, TargetCertificateAt key required result.2.1 input | dist])
    (simulateQ_registeredCacheLedgerImpl_original key required stopAfter computation initial)
  rw [probEvent_map] at hproject
  have hlift : Pr[fun result => result.2.1.2.length ≤ signatureLimit ∧
      ∃ input ∈ result.2.2, TargetCertificateAt key required result.2.1 input |
        (liftM ((simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)) : PMF _)] =
      Pr[fun result => result.2.1.2.length ≤ signatureLimit ∧
      ∃ input ∈ result.2.2, TargetCertificateAt key required result.2.1 input |
        (simulateQ (registeredTargetImpl key) computation).run ((cache, []), ∅)] := by
    simp only [probEvent_eq_tsum_ite]
    rfl
  rw [hlift] at hproject
  rw [← hproject]
  have hcases : ∀ result ∈ law.support,
      (result.2.1.2.1.1.2.length ≤ signatureLimit ∧
        ∃ input ∈ result.2.1.2.1.2, TargetCertificateAt key required result.2.1.2.1.1 input) →
      ((∃ input, result.2.1.2.2.bank input = true) ∨ RegisteredLedgerPrefixExceptional result.2.1.2) ∨ result.2.2 = true := by
    rintro result hresult ⟨hvalid, input, hinput, hcertificate⟩
    rcases registeredSecurityLedgerRun_live_or_exception key required computation cache q hq hfinite hmessage hbound
      result hresult hvalid with hlive | hprefix | hcache
    · have hledger : (result.1, result.2.1) ∈ ledgerLaw.support := by
        dsimp only [ledgerLaw]
        rw [← hforget, PMF.monad_map_eq_map, PMF.mem_support_map_iff]
        exact ⟨result, hresult, rfl⟩
      have hcovered := registeredLedgerRun_covered key required stopAfter computation initial.1
        (by intro _ query hquery; exact False.elim (Finset.notMem_empty query hquery)) _ hledger
      exact Or.inl (Or.inl ⟨input, hcovered hlive input hinput hcertificate⟩)
    · exact Or.inl (Or.inr hprefix)
    · exact Or.inr hcache
  have hmono : Pr[fun result => result.2.1.2.1.1.2.length ≤ signatureLimit ∧
      ∃ input ∈ result.2.1.2.1.2, TargetCertificateAt key required result.2.1.2.1.1 input | law] ≤
      Pr[fun result => ((∃ input, result.2.1.2.2.bank input = true) ∨
        RegisteredLedgerPrefixExceptional result.2.1.2) ∨ result.2.2 = true | law] := by
    simp only [probEvent_eq_tsum_ite]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hr : result ∈ law.support
    · by_cases hp : result.2.1.2.1.1.2.length ≤ signatureLimit ∧
          ∃ input ∈ result.2.1.2.1.2, TargetCertificateAt key required result.2.1.2.1.1 input
      · rw [if_pos hp, if_pos (hcases result hr hp)]
      · rw [if_neg hp]
        exact zero_le
    · have hz : Pr[= result | law] = 0 := by rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]; exact hr
      simp only [hz, ite_self, le_refl]
  exact hmono.trans ((probEvent_or_le law _ _).trans
    (add_le_add ((probEvent_or_le law _ _).trans (add_le_add hbank hprefix)) hcache))

end SphincsSecurity.Concrete
