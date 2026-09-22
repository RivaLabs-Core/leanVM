import SphincsSecurity.Proof.Fts.RegisteredTargets
import SphincsSecurity.Proof.Fts.DigestCompletionCacheGrowth

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

/-- A signing call processed this input, with its result fixed by the cached answers. -/
def ProcessedMessageInput (key : SecretKey) (state : CoverLogState) (input : HashInput) : Prop :=
  ∃ (message : Message) (randomness : Randomness) (response : Option Signature),
    ⟨message, response⟩ ∈ state.2 ∧
    input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) ∧
    ∀ f : QueryImpl HashSpec Id, state.1.AgreesWithFn f →
      let digest := truncateMessageDigest (f input)
      evalWithAnswerFn f (signAfterDigest key randomness (digestIndex digest) (digestLeaves digest)) = response

theorem ProcessedMessageInput.mono (key : SecretKey) (before after : CoverLogState) (input : HashInput)
    (hsource : ProcessedMessageInput key before input) (hcache : before.1 ≤ after.1)
    (hlog : ∀ entry ∈ before.2, entry ∈ after.2) : ProcessedMessageInput key after input := by
  obtain ⟨message, randomness, response, hentry, hinput, hreplay⟩ := hsource
  exact ⟨message, randomness, response, hlog _ hentry, hinput,
    fun f hf => hreplay f (fun _ _ h => hf (hcache h))⟩

/-- Every new admissible signing input has a recorded result, including failure. -/
theorem sign_new_admissible_processed (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (response : Option Signature)
    (hresult : (response, after) ∈ support ((simulateQ romImpl (sign key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    ProcessedMessageInput key (after, [⟨message, response⟩])
      (tweakableHashInput key.parameter .message payload) := by
  rw [sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨selected, loopCache⟩, hloop, hfinish⟩ := hresult
  cases selected with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at hfinish
      obtain ⟨rfl, rfl⟩ := hfinish
      obtain ⟨_, _, _, hselected, _⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
        before after none hloop payload output hbefore hafter hadmissible
      contradiction
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      rw [simulateQ_romImpl_liftM] at hfinish
      have hmessage := signAfterDigest_message_cache_eq key randomness index leaves loopCache after response hfinish payload
      have hpayload := signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before loopCache
        randomness index leaves hloop payload output hbefore (hmessage.symm.trans hafter) hadmissible
      refine ⟨message, randomness, response, by simp, congrArg _ hpayload, ?_⟩
      intro f hf
      have hfinishReplay := replay_of_mem_support (signAfterDigest key randomness index leaves)
        loopCache response after hfinish f hf
      have hloopReplay := replayRom_of_mem_support (signDigestLoop digestAttemptLimit key message)
        before (some (randomness, index, leaves)) loopCache hloop f (fun _ _ h => hf (hfinishReplay.1 h))
      have hgood := successfulDigestLoop_of_mem_support f key message digestAttemptLimit randomness index leaves
        before loopCache after hloopReplay hfinishReplay.1 hf
      obtain ⟨_, digest, heval, _, hindex, hleaves, _⟩ := hgood.extract
      have hdigest : truncateMessageDigest (f (tweakableHashInput key.parameter .message payload)) = digest := by
        rw [hpayload]
        exact heval
      simpa only [hdigest, ← hindex, ← hleaves] using hfinishReplay.2.1

/-- An admissible cached digest was queried directly or processed by the signer. -/
def AdmissibleSources (key : SecretKey) (targets : Finset HashInput) (state : CoverLogState) : Prop :=
  ∀ payload output, state.1 (tweakableHashInput key.parameter .message payload) = some output →
    Admissible (truncateMessageDigest output) →
    tweakableHashInput key.parameter .message payload ∈ targets ∨
      ProcessedMessageInput key state (tweakableHashInput key.parameter .message payload)

theorem AdmissibleSources.after_sign (key : SecretKey) (targets : Finset HashInput)
    (log : QueryLog SigningSpec) (message : Message) (before after : QueryCache HashSpec) (response : Option Signature)
    (hsources : AdmissibleSources key targets (before, log))
    (hsign : (response, after) ∈ support ((simulateQ romImpl (sign key message)).run before)) :
    AdmissibleSources key targets (after, log ++ [⟨message, response⟩]) := by
  intro payload output hafter hadmissible
  have hcache := simulateQ_romImpl_cache_le (sign key message) before (response, after) hsign
  cases hbefore : before (tweakableHashInput key.parameter .message payload) with
  | none =>
      have hsource := sign_new_admissible_processed key message before after response hsign
        payload output hbefore hafter hadmissible
      exact Or.inr (hsource.mono key _ _ _ le_rfl (fun _ h => List.mem_append_right _ h))
  | some previous =>
      have heq : previous = output := Option.some.inj ((hcache hbefore).symm.trans hafter)
      subst previous
      exact (hsources payload output hbefore hadmissible).imp id
        (fun hsource => hsource.mono key _ _ _ hcache (fun _ h => List.mem_append_left _ h))

end SphincsSecurity.Concrete
