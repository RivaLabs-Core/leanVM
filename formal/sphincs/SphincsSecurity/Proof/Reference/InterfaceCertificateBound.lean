import SphincsSecurity.Proof.Reference.RegisteredGameSource
import SphincsSecurity.Proof.Reference.InterfaceMessageCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec FtsProbeSimulation ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs Finset.univ treeRoot

private theorem sampling_bind_run {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld α) >>= next)).run cache =
      computation >>= fun value => (simulateQ romImpl (next value)).run cache := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation from QueryImpl.simulateQ_add_liftM_left _ _ computation,
    unifFwdImpl.simulateQ_run, bind_map_left]

theorem keygen_root_support (generated : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hg : generated ∈ support ((simulateQ romImpl keygen).run ∅)) :
    ∃ parameter otsSecret ftsSecret root,
      root ∈ support ((simulateQ randomOracle (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) ∧
      generated = ((⟨root.1, parameter⟩, ⟨parameter, root.1, otsSecret, ftsSecret⟩), root.2) := by
  rw [keygen, sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨parameter, _, hg⟩ := hg
  rw [sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨otsSecret, _, hg⟩ := hg
  rw [sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨ftsSecret, _, hg⟩ := hg
  rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM, mem_support_bind_iff] at hg
  obtain ⟨root, hroot, hg⟩ := hg
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hg
  exact ⟨parameter, otsSecret, ftsSecret, root, hroot, hg⟩

theorem registeredMessageQueryExpectation_source (key : SecretKey) (publicKey : PublicKey)
    (adversary : Adversary) (cache : QueryCache HashSpec) :
    registeredMessageQueryExpectation key (retainedGameRestComputation adversary publicKey) cache =
      ∑' result, Pr[= result | (simulateQ romImpl (simulateQ (Security.expandSigning (sign key))
        (QueryCap.counted (IsMessageQuery key.parameter) (Seeded.sourceGame publicKey adversary)))).run' cache] * result.2 := by
  rw [Seeded.sourceGame_eq_traced, ← retainedGameRestComputation_verdict_projection,
    QueryCap.counted_map, simulateQ_map, simulateQ_map, StateT.run'_map', tsum_probOutput_map_mul]
  have h := congrArg (fun law : ProbComp (RetainedRestResult × Nat) =>
    ∑' result, Pr[= result | law] * (result.2 : ENNReal))
    (registeredTargetImpl_run'_eq key (QueryCap.counted (IsMessageQuery key.parameter)
      (retainedGameRestComputation adversary publicKey)) ((cache, []), ∅))
  simpa only [StateT.run'_eq, tsum_probOutput_map_mul, registeredMessageQueryExpectation] using h

noncomputable def registeredGameMessageExpectation (adversary : Adversary) : ENNReal :=
  ∑' generated, Pr[= generated | (simulateQ romImpl keygen).run ∅] *
    registeredMessageQueryExpectation generated.1.2 (retainedGameRestComputation adversary generated.1.1) generated.2

theorem registeredGameMessageExpectation_native (adversary : Adversary) :
    registeredGameMessageExpectation adversary =
      ∑' count, Pr[= count | (simulateQ romImpl (interfaceMessageProgram adversary)).run' ∅] * (count : ENNReal) := by
  rw [interfaceMessageProgram, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    map_bind, tsum_probOutput_bind_mul]
  unfold registeredGameMessageExpectation
  apply tsum_congr
  intro generated
  rw [registeredMessageQueryExpectation_source]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, tsum_probOutput_map_mul, StateT.run'_eq]

private theorem expected_count_eq {α : Type} (law : SPMF α) (count : α → Nat)
    (native : ProbComp Nat) (heq : count <$> law = 𝒟[native]) :
    (∑' n, Pr[= n | native] * (n : ENNReal)) =
      ∑' result, Pr[= result | law] * (count result : ENNReal) := by
  have h := congrArg (fun distribution : SPMF Nat => ∑' n, Pr[= n | distribution] * (n : ENNReal)) heq
  rw [tsum_probOutput_map_mul] at h
  simpa only [probOutput_def, SPMF.evalDist_def] using h.symm

theorem registeredGameMessageExpectation_reference (dummy : OtsReferenceWords) (adversary : Adversary) :
    registeredGameMessageExpectation adversary =
      ∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.interfaceMessageCalls : ENNReal) := by
  rw [registeredGameMessageExpectation_native]
  exact expected_count_eq _ _ _ (referenceRecordedGame_native_messageCount dummy adversary)

theorem originalCanonicalCertificate_full_le (original : Security.Adversary) (q : Nat)
    (hq : q ≤ 2 ^ 127) (hbound : Security.HasHashQueryBound original q) (dummy : OtsReferenceWords) :
    let adversary := Seeded.memoAdversary (Security.embed original)
    Pr[fun result => NativeCanonicalCertificate result.1 dummy Finset.univ result.2 |
      originalCertificateSource adversary] ≤
      (2 ^ 128 : ENNReal)⁻¹ * registeredGameMessageExpectation adversary +
      ((q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q) := by
  dsimp only
  let adversary := Seeded.memoAdversary (Security.embed original)
  let loss := (q : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound + 4 * certificateCacheExceptionRate * q
  simp only [originalCertificateSource, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map]
  calc
    _ ≤ ∑' generated, Pr[= generated | (simulateQ romImpl keygen).run ∅] *
        ((2 ^ 128 : ENNReal)⁻¹ * registeredMessageQueryExpectation generated.1.2
          (retainedGameRestComputation adversary generated.1.1) generated.2 + loss) := by
      apply ENNReal.tsum_le_tsum
      intro generated
      by_cases hg : generated ∈ support ((simulateQ romImpl keygen).run ∅)
      · apply mul_le_mul' le_rfl
        obtain ⟨parameter, otsSecret, ftsSecret, root, hroot, rfl⟩ := keygen_root_support generated hg
        simpa only [loss, adversary, Function.comp_def, add_assoc] using nativeCanonicalCertificate_full_le original q hq hbound dummy
          parameter otsSecret ftsSecret root hroot
      · change Pr[= generated | (simulateQ romImpl keygen).run ∅] * _ ≤ _
        rw [probOutput_eq_zero_of_not_mem_support hg, zero_mul, zero_mul]
    _ = (2 ^ 128 : ENNReal)⁻¹ * registeredGameMessageExpectation adversary +
        (∑' generated, Pr[= generated | (simulateQ romImpl keygen).run ∅]) * loss := by
      simp only [registeredGameMessageExpectation, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        mul_left_comm _ ((2 ^ 128 : ENNReal)⁻¹), ENNReal.tsum_mul_left]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' tsum_probOutput_le_one)

end SphincsSecurity.Concrete
