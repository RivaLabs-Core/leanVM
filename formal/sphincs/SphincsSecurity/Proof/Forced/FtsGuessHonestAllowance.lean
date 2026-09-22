import SphincsSecurity.Proof.Reference.TruncatedInterfaceBudget
import SphincsSecurity.Proof.Reference.VerificationHashAllowance

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec OtsContactTrace CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] publicSignPlan

theorem publicSigningRecord_hashCalls_max (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (message : Message) (result : PublicSigningRecord)
    (hr : result ∈ support (publicSigningRecord parameter root f known words selections message)) :
    result.2.hashCalls ≤ 2 ^ 36 := by
  rw [publicSigningRecord, mem_support_bind_iff] at hr
  obtain ⟨loop, hloop, hr⟩ := hr
  let key : SecretKey := ⟨parameter, root, fun _ _ _ _ => 0, fun _ _ _ => 0⟩
  have hc : loop.2.hashCalls ≤ digestAttemptLimit := by
    apply QueryCap.counted_le_of_queryBound _ _ _ (signDigestLoop_hash_bound digestAttemptLimit key message)
      (loop.1, loop.2.hashCalls)
    have hs := support_simulateQ_run'_subset
      ((fixedHashWorld f).liftTarget (StateT PUnit ProbComp))
      (countHashQueries (signDigestLoop digestAttemptLimit key message)) PUnit.unit
    apply hs
    simp only [simulateQ_liftTarget, StateT.run'_eq, StateT.run_liftM, bind_pure_comp, Functor.map_map, id_map']
    rw [← publicDigestLoop_eq key, ← fixedBoundaryRun_count parameter f, support_map]
    exact ⟨loop, hloop, rfl⟩
  cases hs : loop.1 with
  | none =>
      simp only [hs, mem_support_pure_iff] at hr
      subst result
      norm_num [digestAttemptLimit] at hc ⊢
      omega
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [hs, mem_support_pure_iff] at hr
      subst result
      have hp := publicSignPlan_cost_le known words selections randomness index leaves
      simp only [SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]
      norm_num [digestAttemptLimit] at hc ⊢
      omega

namespace FtsGuessHash
open RetainedResidual (IsSigningRequest)

theorem native_run_honest_cost {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (signer : Message → ProbComp (Option Signature × SigningBoundaryTrace))
    (hsigner : ∀ message result, result ∈ support (signer message) → result.2.hashCalls ≤ 2 ^ 36)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cap : Nat)
    (hcap : computation.IsQueryBoundP IsSigningRequest cap)
    (result : (α × SigningBoundaryTrace) × Trace)
    (hr : result ∈ support (((simulateQ (nativeImpl parameter f signer) computation).run).run)) :
    result.1.2.hashCalls ≤ result.2.toList.length + 2 ^ 36 * cap := by
  induction computation using OracleComp.inductionOn generalizing cap result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, mem_support_pure_iff] at hr
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hcap
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map,
        mem_support_bind_iff, support_map] at hr
      obtain ⟨first, hfirst, tail, htail, rfl⟩ := hr
      obtain ⟨tail, htail, rfl⟩ := htail
      have ht := ih first.1.1 _ (hcap.2 first.1.1) tail htail
      have hf : first.1.2.hashCalls ≤ first.2.toList.length +
          2 ^ 36 * (if IsSigningRequest input then 1 else 0) := by
        cases input with
        | inl input =>
            simp only [nativeImpl, WriterT.run_mk, support_map] at hfirst
            obtain ⟨answer, _, rfl⟩ := hfirst
            cases input <;> simp only [signingBoundaryTrace, hashObservationTrace,
              SigningBoundaryTrace.hashCalls, FreeMonoid.toList_one, FreeMonoid.toList_of,
              List.length_nil, List.length_singleton, IsSigningRequest, if_false, Nat.mul_zero,
              Nat.add_zero, le_refl]
        | inr message =>
            simp only [nativeImpl, WriterT.run_mk, support_map] at hfirst
            obtain ⟨record, hrecord, rfl⟩ := hfirst
            simpa only [FreeMonoid.toList_one, List.length_nil, IsSigningRequest, if_true,
              Nat.mul_one, Nat.zero_add] using hsigner message record hrecord
      simp only [SigningBoundaryTrace.hashCalls_mul, FreeMonoid.toList_mul, List.length_append]
      by_cases hs : IsSigningRequest input
      · have hp : 0 < cap := hcap.1.resolve_left (not_not.mpr hs)
        simp only [if_pos hs] at hf ht
        omega
      · simp only [if_neg hs] at hf ht
        omega

attribute [local irreducible] canonicalEncodingInputs canonicalGraphGameInputs canonicalGraphLabels
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

theorem fixed_reference_main_honest_cost (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (before : AdversaryTrace)
    (hr : before ∈ support (simulateQ (fixedAnswers
      (referenceAnswers key.parameter root key.otsSecret labels inputs hencoding auxiliary dummy)
      (FtsGuessSigning.secretTable key.ftsSecret))
      (adversaryRun key.parameter labels ((signingTruncatedAdversary adversary).main ⟨root, key.parameter⟩)))) :
    before.1.2.hashCalls ≤ before.2.toList.length + 2 ^ 36 * signatureLimit := by
  rw [referenceAnswers, fixed_adversaryRun] at hr
  apply native_run_honest_cost key.parameter _ _ _ _ signatureLimit _ before hr
  · intro message record hrecord
    simp only [support_map] at hrecord
    obtain ⟨completed, hcompleted, rfl⟩ := hrecord
    obtain ⟨raw, hraw, rfl⟩ := hcompleted
    dsimp only [Prod.map, Function.id_def]
    rw [completePublicSigningRecord_trace]
    exact publicSigningRecord_hashCalls_max _ _ _ _ _ _ message raw hraw
  · apply (isQueryBoundP_iff_of_map_eq (p := IsSigningRequest)
      (show Prod.fst <$> OtsPrefix.logged ((signingTruncatedAdversary adversary).main ⟨root, key.parameter⟩) =
        (signingTruncatedAdversary adversary).main ⟨root, key.parameter⟩ from by
          rw [CausalFrontierProgram.logged_eq_signingTrace]
          exact FtsProbeSimulation.signingTraceComputation_fst _)).mpr
    exact QueryCap.truncate_queryBound IsSigningRequest _ signatureLimit zeroForgery


theorem fixed_reference_completed_honest_cost (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : Completed)
    (hr : result ∈ support (simulateQ (fixedAnswers
      (referenceAnswers key.parameter root key.otsSecret labels inputs hencoding auxiliary dummy)
      (FtsGuessSigning.secretTable key.ftsSecret))
      (completedRun key.parameter root labels (signingTruncatedAdversary adversary)))) :
    completedWork result ≤ result.1.2.toList.length + 2 ^ 36 * signatureLimit + 2 ^ 16 := by
  rw [completedRun, simulateQ_bind, mem_support_bind_iff] at hr
  obtain ⟨before, hb, hr⟩ := hr
  have hm := fixed_reference_main_honest_cost key root inputs hencoding labels auxiliary dummy adversary before hb
  simp only [simulateQ_bind, referenceAnswers, fixed_verifyProgram, pure_bind, simulateQ_pure,
    mem_support_pure_iff] at hr
  subst result
  have hv := boundaryEval_hashCalls_le_query_bound key.parameter
    (programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
    (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) (2 ^ 16)
    (verify_hash_query_bound _ _ _)
  dsimp only [completedWork]
  omega

end FtsGuessHash
end SphincsSecurity.Concrete
