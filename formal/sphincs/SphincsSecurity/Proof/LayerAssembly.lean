import SphincsSecurity.Proof.SignatureLayout
open OracleComp OracleSpec
namespace SphincsSecurity
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def restrictPath (lay : Layer) (path : Fin maxLayerHeight → α) : Fin (layerHeight lay) → α :=
  fun level => path (level.castLE (layerHeight_le lay))

theorem sequenceFin_restrictPath {m : Type → Type} [Monad m] [LawfulMonad m]
    (lay : Layer) (values : Fin maxLayerHeight → m α) (default : α) :
    restrictPath lay <$> Concrete.sequenceFin (fun level =>
      if level.val < layerHeight lay then values level else pure default) =
      Concrete.sequenceFin (fun level : Fin (layerHeight lay) => values (level.castLE (layerHeight_le lay))) := by
  fin_cases lay <;>
    simp [layerHeight, maxLayerHeight, Concrete.sequenceFin, map_bind]
  all_goals repeat' (apply bind_congr; intro value)
  all_goals congr 1
  all_goals
    funext value level
    fin_cases level <;> rfl

theorem sequenceLayers_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Layer → Type} (f : (lay : Layer) → α lay → β lay)
    (computation : (lay : Layer) → m (α lay)) :
    Concrete.sequenceLayers (fun lay => f lay <$> computation lay) =
      (fun parts lay => f lay (parts lay)) <$> Concrete.sequenceLayers computation := by
  simp only [Concrete.sequenceLayers, bind_map_left, map_bind, map_pure]
  refine bind_congr fun bottom => bind_congr fun middle => bind_congr fun top => ?_
  congr 1
  funext lay
  fin_cases lay <;> rfl

end SphincsSecurity
