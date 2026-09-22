import SphincsSecurity.Proof.Base.QueryCap

namespace SphincsSecurity.QueryCap

open OracleComp OracleSpec

variable {ι : Type} {spec : OracleSpec ι} {selected : ι → Prop}

inductive Uncharged {α : Type} : OracleComp spec α → Prop
  | pure (value : α) : Uncharged (pure value)
  | query (input : ι) (hfree : ¬selected input) (next : spec.Range input → OracleComp spec α)
      (tail : ∀ answer, Uncharged (next answer)) : Uncharged (liftM (spec.query input) >>= next)

theorem Uncharged.bind {α β : Type} {first : OracleComp spec α} (hfirst : Uncharged (selected := selected) first)
    (next : α → OracleComp spec β) (hnext : ∀ value, Uncharged (selected := selected) (next value)) :
    Uncharged (selected := selected) (first >>= next) := by
  induction hfirst with
  | pure value => simpa only [pure_bind] using hnext value
  | query input hfree tail _ ih => simpa only [bind_assoc] using Uncharged.query input hfree _ ih

theorem Uncharged.map {α β : Type} {first : OracleComp spec α} (hfirst : Uncharged (selected := selected) first)
    (f : α → β) : Uncharged (selected := selected) (f <$> first) := by
  simpa only [bind_pure_comp] using hfirst.bind (fun value => Pure.pure (f value)) (fun value => .pure (f value))

theorem Uncharged.query_pure (input : ι) (hfree : ¬selected input) :
    Uncharged (selected := selected) (liftM (spec.query input) : OracleComp spec _) := by
  simpa only [bind_pure] using Uncharged.query input hfree Pure.pure Uncharged.pure

theorem Uncharged.counted {α : Type} [DecidablePred selected] {computation : OracleComp spec α}
    (h : Uncharged (selected := selected) computation) :
    QueryCap.counted selected computation = (fun value => (value, 0)) <$> computation := by
  induction h with
  | pure value => rfl
  | query input hfree next _ ih =>
    simp only [counted_query_bind, if_neg hfree, Nat.zero_add, ih, bind_pure_comp, Functor.map_map, map_bind]

end SphincsSecurity.QueryCap
