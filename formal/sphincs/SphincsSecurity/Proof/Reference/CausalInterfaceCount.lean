import SphincsSecurity.Proof.Reference.InterfaceFixedBudget
import SphincsSecurity.Proof.Reference.CausalFrontierProgram
import SphincsSecurity.Proof.Hypertree.FrontierRandomOracle
import SphincsSecurity.Proof.Base.Uncharged

namespace SphincsSecurity.Concrete.CausalFrontierProgram

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {α : Type}

theorem probability_uncharged (computation : ProbComp α) :
    QueryCap.Uncharged (selected := Security.IsHash) (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
    rw [liftM_bind]
    exact QueryCap.Uncharged.query (spec := OracleWorld) (selected := Security.IsHash)
      (Sum.inl input) (by simp [Security.IsHash]) _ ih

theorem counted_adversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Seeded.FtsSecrets)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (input : (OracleWorld + SigningSpec).Domain) :
    QueryCap.counted Security.IsHash (adversaryImpl parameter root external ftsSecret words frontier input).run =
      (fun result => (result, if Security.IsAdversaryHash input then 1 else 0)) <$>
        (adversaryImpl parameter root external ftsSecret words frontier input).run := by
  cases input with
  | inl world =>
    simp only [adversaryImpl, QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_liftM,
      bind_pure_comp, QueryImpl.id'_apply]
    cases world <;> rfl
  | inr message =>
    exact (probability_uncharged _).counted

theorem counted_interface (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Seeded.FtsSecrets)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    QueryCap.counted Security.IsHash
      (simulateQ (adversaryImpl parameter root external ftsSecret words frontier) computation).run =
      (fun result => ((result.1.1, result.2), result.1.2)) <$>
        (simulateQ (adversaryImpl parameter root external ftsSecret words frontier)
          (QueryCap.counted Security.IsAdversaryHash computation)).run :=
  QueryCap.counted_writer_simulateQ _ _ _ (counted_adversaryImpl parameter root external ftsSecret words frontier) computation

theorem logged_eq_signingTrace (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OtsPrefix.logged computation = FtsProbeSimulation.signingTraceComputation computation := by
  rw [OtsPrefix.logged, FtsProbeSimulation.simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    simulateQ_id']

theorem gameRest_eq_interface (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Seeded.FtsSecrets)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    gameRest parameter root external ftsSecret words frontier adversary =
      (simulateQ (adversaryImpl parameter root external ftsSecret words frontier)
        (Seeded.sourceGame ⟨root, parameter⟩ adversary)).run := by
  rw [Seeded.sourceGame_eq_traced, FtsProbeSimulation.tracedGameRestComputation,
    gameRest, adversaryRun, logged_eq_signingTrace, simulateQ_bind, WriterT.run_bind]
  apply bind_congr
  intro result
  have hlift : simulateQ (adversaryImpl parameter root external ftsSecret words frontier)
      (FtsProbeSimulation.liftOracleWorldLeft
        (scheme.verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature)) =
      simulateQ ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter))
        (scheme.verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature) := by
    have himpl : adversaryImpl parameter root external ftsSecret words frontier =
        (QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) +
          (fun message => WriterT.mk (liftM (frontierSigningRun parameter root
            (maskOtsPrefixes parameter words external) ftsSecret words frontier message) : OracleComp OracleWorld _)) := by
      funext input
      cases input <;> rfl
    rw [himpl]
    exact FtsProbeSimulation.simulateQ_liftOracleWorldLeft
      ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter))
      (fun message => WriterT.mk (liftM (frontierSigningRun parameter root
        (maskOtsPrefixes parameter words external) ftsSecret words frontier message) : OracleComp OracleWorld _)) _
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map, hlift, Functor.map_map]
  rfl

theorem fixed_interface (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (fixedHashWorld f)
      (simulateQ (adversaryImpl key.parameter key.root f key.ftsSecret words frontier) computation).run =
      fixedBoundaryRun key.parameter f
        (simulateQ (Security.expandSigning (sign key)) computation) := by
  have hquery : ∀ input, simulateQ (fixedHashWorld f)
      (adversaryImpl key.parameter key.root f key.ftsSecret words frontier input).run =
        (causalFrontierAdversaryImpl key.parameter key.root f key.ftsSecret words frontier input).run := by
    intro input
    cases input with
    | inl world => simp [adversaryImpl, causalFrontierAdversaryImpl, QueryImpl.withTrace_apply]
    | inr message =>
      exact simulateQ_fixedHashWorld_lift_prob f _
  rw [simulateQ_writer_compose _ _ _ hquery, causalFrontierAdversaryImpl_eq]
  have hhandler : frontierAdversaryImpl key.parameter key.root f key.ftsSecret words frontier =
      ((fixedHashWorld f).withTrace (signingBoundaryTrace key.parameter)) ∘ₛ
        Security.expandSigning (sign key) := by
    funext input
    have h := simulateQ_expandedAdversaryImpl_frontier key f words frontier hfrontier hwords input
    cases input <;> exact h.symm
  rw [hhandler, QueryImpl.simulateQ_compose]
  rfl

theorem fixed_counted_interface_forget (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (fun result => (result.1.1, result.2)) <$>
      simulateQ (fixedHashWorld f) (QueryCap.counted Security.IsHash
        (simulateQ (adversaryImpl key.parameter key.root f key.ftsSecret words frontier) computation).run) =
      simulateQ (fixedHashWorld f) (simulateQ (Security.expandSigning (sign key))
        (QueryCap.counted Security.IsAdversaryHash computation)) := by
  rw [counted_interface, simulateQ_map, Functor.map_map, fixed_interface key f words frontier hfrontier hwords]
  exact fixedBoundaryRun_forget _ _ _

theorem fixed_gameRest_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (key : SecretKey) (f : QueryImpl HashSpec Id)
    (hroot : key.root = evalWithAnswerFn f
      (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)))
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (simulateQ (fixedHashWorld f) (QueryCap.counted Security.IsHash
      (gameRest key.parameter key.root f key.ftsSecret words frontier
        (Seeded.memoAdversary (Security.embed adversary)))))) : result.2 ≤ q := by
  have h := fixedInterface_counted_budget adversary q hsmall hbound key.parameter key.otsSecret key.ftsSecret f
  dsimp only at h
  rw [← hroot] at h
  apply h (result.1.1, result.2)
  rw [← fixed_counted_interface_forget key f words frontier hfrontier hwords, support_map]
  exact ⟨result, by rwa [gameRest_eq_interface] at hresult, rfl⟩

theorem fixed_game_counted_budget (adversary : Security.Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : Security.HasHashQueryBound adversary q)
    (key : SecretKey) (f : QueryImpl HashSpec Id)
    (hroot : key.root = evalWithAnswerFn f
      (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)))
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (simulateQ (fixedHashWorld f) (QueryCap.counted Security.IsHash
      (game key.parameter f key.ftsSecret words frontier
        (Seeded.memoAdversary (Security.embed adversary)))))) : result.2 ≤ q := by
  rw [game, QueryCap.counted_map, simulateQ_map, support_map] at hresult
  obtain ⟨rest, hrest, rfl⟩ := hresult
  rw [← frontierRoot_eq_of_agree key.parameter words f (maskOtsPrefixes key.parameter words f)
    (maskOtsPrefixes_agrees key.parameter words f), frontierRoot_eq key f words frontier hfrontier,
    ← hroot] at hrest
  exact fixed_gameRest_counted_budget adversary q hsmall hbound key f hroot words frontier hfrontier hwords rest hrest

end SphincsSecurity.Concrete.CausalFrontierProgram
