import SphincsSecurity.Proof.Reference.ReferenceInterfaceBudget
import SphincsSecurity.Proof.Reference.RegisteredGameBudget
import SphincsSecurity.Proof.Reference.ReferenceCertificateTrace

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs treeRoot honestNode

namespace CausalFrontierProgram

variable {α : Type}

theorem message_probability_uncharged (parameter : PublicParameter) (computation : ProbComp α) :
    QueryCap.Uncharged (selected := IsInterfaceMessage parameter) (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
    rw [liftM_bind]
    exact QueryCap.Uncharged.query (spec := OracleWorld) (selected := IsInterfaceMessage parameter)
      (Sum.inl input) (by simp [IsInterfaceMessage, Security.IsHash]) _ ih

theorem counted_message_adversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Seeded.FtsSecrets)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (input : (OracleWorld + SigningSpec).Domain) :
    QueryCap.counted (IsInterfaceMessage parameter) (adversaryImpl parameter root external ftsSecret words frontier input).run =
      (fun result => (result, if IsMessageQuery parameter input then 1 else 0)) <$>
        (adversaryImpl parameter root external ftsSecret words frontier input).run := by
  cases input with
  | inl world =>
    simp only [adversaryImpl, QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_liftM,
      bind_pure_comp, QueryImpl.id'_apply, WriterT.run_map, WriterT.run_tell, map_pure,
      ]
    cases world with
    | inl sample =>
      simp only [QueryCap.counted_map, QueryCap.counted_query, IsInterfaceMessage, Security.IsHash,
        false_and, IsMessageQuery, if_false, Functor.map_map]
    | inr hash =>
      simp only [QueryCap.counted_map, QueryCap.counted_query, IsInterfaceMessage, Security.IsHash,
        NonmessageHash, IsMessageQuery, true_and, not_not, Functor.map_map]
  | inr message =>
    simp only [IsMessageQuery, if_false]
    exact (message_probability_uncharged parameter _).counted

theorem counted_message_interface (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Seeded.FtsSecrets)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    QueryCap.counted (IsInterfaceMessage parameter)
      (simulateQ (adversaryImpl parameter root external ftsSecret words frontier) computation).run =
      (fun result => ((result.1.1, result.2), result.1.2)) <$>
        (simulateQ (adversaryImpl parameter root external ftsSecret words frontier)
          (QueryCap.counted (IsMessageQuery parameter) computation)).run :=
  QueryCap.counted_writer_simulateQ _ _ _ (counted_message_adversaryImpl parameter root external ftsSecret words frontier) computation

theorem fixed_counted_message_forget (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (fun result => (result.1.1, result.2)) <$>
      simulateQ (fixedHashWorld f) (QueryCap.counted (IsInterfaceMessage key.parameter)
        (simulateQ (adversaryImpl key.parameter key.root f key.ftsSecret words frontier) computation).run) =
      simulateQ (fixedHashWorld f) (simulateQ (Security.expandSigning (sign key))
        (QueryCap.counted (IsMessageQuery key.parameter) computation)) := by
  rw [counted_message_interface, simulateQ_map, Functor.map_map, fixed_interface key f words frontier hfrontier hwords]
  exact fixedBoundaryRun_forget _ _ _

theorem fixed_game_message_count (key : SecretKey) (f : QueryImpl HashSpec Id)
    (hroot : key.root = evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)))
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (adversary : Adversary) :
    Prod.snd <$> simulateQ (fixedHashWorld f) (QueryCap.counted (IsInterfaceMessage key.parameter)
      (game key.parameter f key.ftsSecret words frontier adversary)) =
      Prod.snd <$> simulateQ (fixedHashWorld f) (simulateQ (Security.expandSigning (sign key))
        (QueryCap.counted (IsMessageQuery key.parameter) (Seeded.sourceGame ⟨key.root, key.parameter⟩ adversary))) := by
  rw [game, QueryCap.counted_map, simulateQ_map, Functor.map_map,
    ← frontierRoot_eq_of_agree key.parameter words f (maskOtsPrefixes key.parameter words f)
      (maskOtsPrefixes_agrees key.parameter words f), frontierRoot_eq key f words frontier hfrontier, ← hroot,
    gameRest_eq_interface, ← fixed_counted_message_forget key f words frontier hfrontier hwords, Functor.map_map]

end CausalFrontierProgram

theorem referenceRecordedRest_messageCount (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let root := evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree))
    let rooted : SecretKey := { key with root := root }
    (fun result => QueryCap.calls (IsInterfaceMessage key.parameter) result.2) <$>
      referenceRecordedRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
        (referenceTableSelection key f) dummy adversary =
      Prod.snd <$> simulateQ (fixedHashWorld f)
        (simulateQ (Security.expandSigning (sign rooted))
          (QueryCap.counted (IsMessageQuery key.parameter)
            (Seeded.sourceGame ⟨root, key.parameter⟩ adversary))) := by
  dsimp only
  let root := evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree))
  let rooted : SecretKey := { key with root := root }
  have hw : referenceFamilyWords (referenceTableSelection key f) dummy = canonicalReferenceWords rooted f dummy := by
    rw [referenceFamilyWords_selected]
    exact (ReferenceVerifierWitness.canonicalReferenceWords_root key f root dummy).symm
  rw [referenceRecordedRest, hw, canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root]
  have h := CausalFrontierProgram.fixed_game_message_count rooted f rfl
    (canonicalReferenceWords rooted f dummy)
    (canonicalFrontierValues rooted f (canonicalReferenceWords rooted f dummy))
    (isSigningFrontier_canonical rooted f _) (frontierReferenceWord_canonical rooted f dummy) adversary
  rw [← QueryCap.recorded_counted, simulateQ_map, Functor.map_map] at h
  exact h

noncomputable def interfaceMessageProgram (adversary : Adversary) : OracleComp OracleWorld Nat := do
  let generated ← keygen
  Prod.snd <$> simulateQ (Security.expandSigning (sign generated.2))
    (QueryCap.counted (IsMessageQuery generated.2.parameter) (Seeded.sourceGame generated.1 adversary))

noncomputable def fixedInterfaceMessageGame (f : QueryImpl HashSpec Id) (adversary : Adversary) : ProbComp Nat := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  Prod.snd <$> simulateQ (fixedHashWorld f) (simulateQ (Security.expandSigning (sign key))
    (QueryCap.counted (IsMessageQuery parameter) (Seeded.sourceGame ⟨key.root, parameter⟩ adversary)))

theorem simulateQ_interfaceMessageProgram (f : QueryImpl HashSpec Id) (adversary : Adversary) :
    simulateQ (fixedHashWorld f) (interfaceMessageProgram adversary) = fixedInterfaceMessageGame f adversary := by
  rw [interfaceMessageProgram, keygen, fixedInterfaceMessageGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob, fixedHashWorld_lift_hash_eq_pure,
    simulateQ_map, bind_assoc, pure_bind]

theorem referenceRecordedGame_messageCount (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceRecordedResult.interfaceMessageCalls <$> referenceRecordedGame inputs hencoding dummy adversary =
      𝒟[do
        let table ← sampleHashTable inputs
        fixedInterfaceMessageGame (finiteHashAnswer ∅ inputs table) adversary] := by
  rw [referenceRecordedGame]
  simp only [map_bind, map_pure, fixedInterfaceMessageGame]
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  simp only [ReferenceRecordedResult.interfaceMessageCalls, bind_pure_comp, ← evalDist_map]
  have hselected := referenceFamilyOracleSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter)
    (fun selections table => (fun result => QueryCap.calls (IsInterfaceMessage parameter) result.2) <$>
      referenceRecordedRest ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary)
  rw [hselected]
  apply evalDist_bind_congr_left
  intro table
  exact congrArg evalDist (
    referenceRecordedRest_messageCount ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs table) dummy adversary)

noncomputable def interfaceMessageResultProgram (adversary : Adversary) : OracleComp OracleWorld (Bool × Nat) := do
  let generated ← keygen
  simulateQ (Security.expandSigning (sign generated.2))
    (QueryCap.counted (IsMessageQuery generated.2.parameter) (Seeded.sourceGame generated.1 adversary))

theorem interfaceMessageResultProgram_count (adversary : Adversary) :
    Prod.snd <$> interfaceMessageResultProgram adversary = interfaceMessageProgram adversary := by
  simp only [interfaceMessageResultProgram, interfaceMessageProgram, map_bind]

theorem interfaceMessageResultProgram_verdict (adversary : Adversary) :
    Prod.fst <$> interfaceMessageResultProgram adversary = gameCore scheme adversary := by
  rw [interfaceMessageResultProgram, gameCore_eq]
  simp only [map_bind, ← simulateQ_map, QueryCap.counted_forget]
  apply bind_congr
  intro generated
  have himpl : Security.expandSigning (sign generated.2) = expandedAdversaryImpl generated.2 := by
    funext input
    cases input with
    | inl world => cases world <;> rfl
    | inr message => rfl
  rw [Seeded.sourceGame_eq_traced, himpl]
  unfold FtsProbeSimulation.tracedGameRestComputation gameRest
  rw [simulateQ_bind,
    ← FtsProbeSimulation.simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend]
  apply bind_congr
  rintro ⟨forgery, log⟩
  rw [simulateQ_bind, FtsProbeSimulation.simulateQ_expanded_liftOracleWorldLeft]
  simp only [simulateQ_pure]

theorem interfaceMessageProgram_hashInputs (adversary : Adversary) :
    hashInputs (interfaceMessageProgram adversary) = hashInputs (boundaryGameCore adversary) := by
  rw [← interfaceMessageResultProgram_count, ResidualByteFrontend.hashInputs_map,
    ← ResidualByteFrontend.hashInputs_map Prod.fst, interfaceMessageResultProgram_verdict,
    ← boundaryGameCore_fst, ResidualByteFrontend.hashInputs_map]

theorem referenceRecordedGame_native_messageCount (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceRecordedResult.interfaceMessageCalls <$>
      referenceRecordedGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary =
        𝒟[(simulateQ romImpl (interfaceMessageProgram adversary)).run' ∅] := by
  rw [referenceRecordedGame_messageCount _ _ (canonicalGraphInputs_subset_gameInputs adversary),
    evalDist_romRun_eq_finiteHash _ (canonicalGraphGameInputs adversary)
      (by rw [interfaceMessageProgram_hashInputs]; exact hashInputs_subset_canonicalGraphGameInputs adversary) ∅]
  apply evalDist_bind_congr_left
  intro table
  exact congrArg evalDist (simulateQ_interfaceMessageProgram (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary) table) adversary).symm

end SphincsSecurity.Concrete
