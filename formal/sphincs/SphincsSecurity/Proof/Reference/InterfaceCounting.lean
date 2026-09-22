import SphincsSecurity.Proof.Reference.QueryAllocation

namespace SphincsSecurity.QueryCap

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ}

theorem counted_simulateQ {α : Type} (selectedSource : ι → Prop) [DecidablePred selectedSource]
    (selectedTarget : κ → Prop) [DecidablePred selectedTarget] (impl : QueryImpl source (OracleComp target))
    (himpl : ∀ input, counted selectedTarget (impl input) =
      (fun value => (value, if selectedSource input then 1 else 0)) <$> impl input)
    (computation : OracleComp source α) :
    counted selectedTarget (simulateQ impl computation) = simulateQ impl (counted selectedSource computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    conv_rhs => rw [counted_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, counted_bind, himpl, bind_map_left, ih, simulateQ_pure]

theorem counted_writer_simulateQ {α Trace : Type} [Monoid Trace]
    (selectedSource : ι → Prop) [DecidablePred selectedSource]
    (selectedTarget : κ → Prop) [DecidablePred selectedTarget]
    (impl : QueryImpl source (WriterT Trace (OracleComp target)))
    (himpl : ∀ input, counted selectedTarget (impl input).run =
      (fun value => (value, if selectedSource input then 1 else 0)) <$> (impl input).run)
    (computation : OracleComp source α) :
    counted selectedTarget (simulateQ impl computation).run =
      (fun result => ((result.1.1, result.2), result.1.2)) <$>
        (simulateQ impl (counted selectedSource computation)).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    conv_rhs => rw [counted_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind,
      counted_bind, himpl, bind_map_left, counted_map, ih, simulateQ_map, WriterT.run_map,
      bind_pure_comp, map_bind, Functor.map_map]

theorem recorded_two_counts {α : Type} (first second : ι → Prop) [DecidablePred first] [DecidablePred second]
    (computation : OracleComp source α) :
    (fun result => ((result.1, calls first result.2), calls second result.2)) <$> recorded computation =
      counted second (counted first computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [recorded_query_bind, counted_query_bind, counted_map, map_bind, calls_cons,
      bind_pure_comp, Functor.map_map]
    congr 1
    funext answer
    rw [← ih answer]
    simp only [Functor.map_map]

theorem calls_mono {first second : ι → Prop} [DecidablePred first] [DecidablePred second]
    (h : ∀ input, first input → second input) (inputs : List ι) : calls first inputs ≤ calls second inputs := by
  induction inputs with
  | nil => exact le_rfl
  | cons input inputs ih =>
    simp only [calls_cons]
    by_cases hf : first input
    · simp only [if_pos hf, if_pos (h input hf)]
      omega
    · simp only [if_neg hf, Nat.zero_add]
      omega

theorem counted_support_mono {α State : Type} (first second : ι → Prop) [DecidablePred first] [DecidablePred second]
    (hselected : ∀ input, first input → second input) (impl : QueryImpl source (StateT State ProbComp))
    (computation : OracleComp source α) (state : State) (result : ((α × Nat) × Nat) × State)
    (hresult : result ∈ support ((simulateQ impl (counted first (counted second computation))).run state)) :
    result.1.2 ≤ result.1.1.2 := by
  rw [← recorded_two_counts, simulateQ_map, StateT.run_map, support_map] at hresult
  obtain ⟨trace, htrace, rfl⟩ := hresult
  exact calls_mono hselected trace.1.2

end SphincsSecurity.QueryCap
