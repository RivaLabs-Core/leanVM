import SphincsSecurity.Proof.Residual.RetainedResidualPrimitivePotential
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.RetainedResidual
open OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition

def Memory.honestHashes (memory : Memory) : Nat :=
  keygenHashCost + (memory.records.map (fun record => record.2.2.hashCalls)).sum

def Memory.honestMessages (memory : Memory) : Nat :=
  (memory.records.map (fun record => record.2.2.messageCalls.length)).sum

def Memory.interfaceHashes (memory : Memory) : Nat := memory.external.hashCalls - memory.honestHashes

def Memory.interfaceMessages (memory : Memory) : Nat := memory.messageCalls.length - memory.honestMessages

def InterfaceResources (memory : Memory) : Prop :=
  memory.honestHashes ≤ memory.external.hashCalls ∧ memory.honestMessages ≤ memory.messageCalls.length ∧
    memory.external.probes + memory.interfaceMessages ≤ memory.interfaceHashes

theorem honestHashes_recordSigning (memory : Memory) (message : Message) (record : SigningRecord) :
    (memory.recordSigning message record).honestHashes = memory.honestHashes + record.2.hashCalls := by
  simp only [Memory.honestHashes, Memory.recordSigning, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]

theorem honestMessages_recordSigning (memory : Memory) (message : Message) (record : SigningRecord) :
    (memory.recordSigning message record).honestMessages = memory.honestMessages + record.2.messageCalls.length := by
  simp only [Memory.honestMessages, Memory.recordSigning, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem interfaceHashes_signing (memory : Memory) (message : Message) (record : SigningRecord) :
    ((memory.applyBoundary record.2).recordSigning message record).interfaceHashes = memory.interfaceHashes := by
  rw [Memory.interfaceHashes, honestHashes_recordSigning]
  change memory.external.hashCalls + record.2.hashCalls - (memory.honestHashes + record.2.hashCalls) = _
  exact Nat.add_sub_add_right _ _ _

theorem interfaceMessages_signing (memory : Memory) (message : Message) (record : SigningRecord) :
    ((memory.applyBoundary record.2).recordSigning message record).interfaceMessages = memory.interfaceMessages := by
  rw [Memory.interfaceMessages, honestMessages_recordSigning]
  change (memory.messageCalls ++ record.2.messageCalls).length - (memory.honestMessages + record.2.messageCalls.length) = _
  rw [List.length_append]
  exact Nat.add_sub_add_right _ _ _

theorem InterfaceResources.signing {memory : Memory} (h : InterfaceResources memory)
    (message : Message) (record : SigningRecord) :
    InterfaceResources ((memory.applyBoundary record.2).recordSigning message record) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [honestHashes_recordSigning]
    exact Nat.add_le_add_right h.1 _
  · rw [honestMessages_recordSigning]
    change memory.honestMessages + record.2.messageCalls.length ≤ (memory.messageCalls ++ record.2.messageCalls).length
    rw [List.length_append]
    exact Nat.add_le_add_right h.2.1 _
  · rw [interfaceMessages_signing, interfaceHashes_signing]
    exact h.2.2

theorem honestHashes_afterReply (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) :
    (memory.afterReply parameter input answer external).honestHashes = memory.honestHashes := by
  cases answer <;> simp only [Memory.afterReply, Option.elim_none, Option.elim_some, Memory.observeMessage]
  · rfl
  · split <;> rfl

theorem honestMessages_afterReply (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) :
    (memory.afterReply parameter input answer external).honestMessages = memory.honestMessages := by
  cases answer <;> simp only [Memory.afterReply, Option.elim_none, Option.elim_some, Memory.observeMessage]
  · rfl
  · split <;> rfl

theorem InterfaceResources.initial (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) : InterfaceResources (initialState inputs words exposed).memory := by
  simp only [InterfaceResources, Memory.honestHashes, Memory.honestMessages, Memory.interfaceHashes,
    Memory.interfaceMessages, initialState, initialMemory, List.map_nil, List.sum_nil, List.length_nil,
    Nat.add_zero, Nat.sub_self, le_refl, and_self]

theorem afterReply_messageCount_ge (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) :
    memory.messageCalls.length ≤ (memory.afterReply parameter input answer external).messageCalls.length := by
  cases answer <;> by_cases hm : FtsProbeSimulation.MessageHashInput parameter input <;>
    simp [Memory.afterReply, Memory.observeMessage, hm]

theorem afterReply_interfaceMessages (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) (hresources : InterfaceResources memory) :
    (memory.afterReply parameter input answer external).interfaceMessages = memory.interfaceMessages +
      answer.elim 0 (fun _ => if FtsProbeSimulation.MessageHashInput parameter input then 1 else 0) := by
  have hm := hresources.2.1
  unfold Memory.honestMessages at hm
  cases answer <;> by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input <;>
    simp only [Memory.afterReply, Option.elim_none, Option.elim_some, Memory.observeMessage,
      hmessage, reduceIte, Memory.interfaceMessages, Memory.honestMessages,
      List.length_append, List.length_singleton, Nat.add_zero]
  omega

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_interfaceHashes (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hresources : InterfaceResources state.memory) :
    (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.interfaceHashes =
      state.memory.interfaceHashes + 1 := by
  have hh := checkedHashResult_hashCalls parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hm := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have ho := congrArg Memory.honestHashes hm
  rw [honestHashes_afterReply] at ho
  simp only [Memory.interfaceHashes, hh, ho]
  have hb := hresources.1
  omega

theorem checkedHashResult_interfaceResources (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hresources : InterfaceResources state.memory) :
    InterfaceResources (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory := by
  let result := checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hp := checkedHashResult_probes parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hh := checkedHashResult_hashCalls parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hmemory := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have ho := congrArg Memory.honestHashes hmemory
  have hom := congrArg Memory.honestMessages hmemory
  rw [honestHashes_afterReply] at ho
  rw [honestMessages_afterReply] at hom
  have hupper := afterReply_messageCount_le parameter state.memory input.val result.1 result.2.memory.external
  have hlower := afterReply_messageCount_ge parameter state.memory input.val result.1 result.2.memory.external
  rw [← hmemory] at hupper hlower
  obtain ⟨hcost, hmessages, hresources⟩ := hresources
  refine ⟨?_, ?_, ?_⟩
  · rw [ho, hh]; omega
  · rw [hom]; exact hmessages.trans hlower
  · simp only [Memory.interfaceHashes, Memory.interfaceMessages, hh, ho, hom] at hresources ⊢
    by_cases hm : FtsProbeSimulation.MessageHashInput parameter input.val
    · rw [if_pos hm] at hupper
      rw [hp, charge_message_probes parameter words routing input.val hm]
      omega
    · rw [if_neg hm] at hupper
      have hprobes := charge_probes_le parameter words routing.disclosed routing.known input.val state.memory.external
      rw [hp]
      omega


theorem lazyByteRun_world_interfaceResources (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (hbound : InterfaceResources state.memory)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state result ≠ 0) : InterfaceResources result.2.memory := by
  cases input with
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [lazyByteRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbound
  | inr input =>
      have hin : input ∈ inputs := by
        apply hinputs
        rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
        exact mem_hashInputs_hash_bind input pure
      obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows routing input hin state ha result hresult
      exact checkedHashResult_interfaceResources parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hbound

omit parameter hencoding in
theorem lazyRun_signingProgram_interfaceResources (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : InterfaceResources state.memory)
    (result : Option (Option Signature) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0) :
    InterfaceResources result.2.memory := by
  rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨raw, hraw, hresult⟩ := hresult
  have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key state.memory.routing.known words selections message).trans hinputs
  rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
  obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key.root message hloop state ha hcovered raw hraw
  simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  change InterfaceResources (raw.2.memory.recordSigning message record)
  rw [hmemory]
  exact hbound.signing message record

omit parameter hencoding in
theorem lazyRun_request_interfaceResources (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : InterfaceResources state.memory)
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) : InterfaceResources result.2.memory := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      exact lazyByteRun_world_interfaceResources key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha hbound result hresult
  | inr message =>
      exact lazyRun_signingProgram_interfaceResources inputs words publicReplies selections rows key hencoding message hinputs state
        ha hcovered hbound result hresult


theorem lazyByteRun_world_interfaceHashes (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (hbound : InterfaceResources state.memory)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state result ≠ 0) :
    result.2.memory.interfaceHashes = state.memory.interfaceHashes + (if input matches .inr _ then 1 else 0) := by
  cases input with
  | inl input =>
    rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
    obtain ⟨answer, _, hresult⟩ := hresult
    rw [lazyByteRun_pure] at hresult
    simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
    subst result
    exact (Nat.add_zero _).symm
  | inr input =>
    have hin : input ∈ inputs := by
      apply hinputs
      rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
      exact mem_hashInputs_hash_bind input pure
    obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows routing input hin state ha result hresult
    exact checkedHashResult_interfaceHashes parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hbound

omit parameter hencoding in
theorem lazyRun_signingProgram_interfaceHashes (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option (Option Signature) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0) :
    result.2.memory.interfaceHashes = state.memory.interfaceHashes := by
  rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨raw, hraw, hresult⟩ := hresult
  have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key state.memory.routing.known words selections message).trans hinputs
  rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
  obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key.root message hloop state ha hcovered raw hraw
  simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  change (raw.2.memory.recordSigning message record).interfaceHashes = _
  rw [hmemory, interfaceHashes_signing]

omit parameter hencoding in
theorem lazyRun_request_interfaceHashes (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : InterfaceResources state.memory)
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    result.2.memory.interfaceHashes = state.memory.interfaceHashes + (if Security.IsAdversaryHash input then 1 else 0) := by
  cases input with
  | inl input =>
    change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
    rw [lazyRun_externalProgram] at hresult
    have h := lazyByteRun_world_interfaceHashes key.parameter inputs hencoding words publicReplies selections rows
      state.memory.routing input hinputs state ha hbound result hresult
    cases input <;> exact h
  | inr message =>
    simpa only [Security.IsAdversaryHash, if_false, Nat.add_zero] using
      lazyRun_signingProgram_interfaceHashes inputs words publicReplies selections rows key hencoding message hinputs state ha hcovered result hresult


end SphincsSecurity.Concrete.RetainedResidual
