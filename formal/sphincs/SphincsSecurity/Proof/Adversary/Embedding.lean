import SphincsSecurity.Proof.Adversary.Accounting

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security
set_option backward.isDefEq.respectTransparency false

def embed (adversary : Adversary) : SphincsSecurity.Adversary :=
  ⟨adversary.main⟩

theorem game_embed (adversary : Adversary) :
    SphincsSecurity.gameCore Seeded.scheme (embed adversary) = gameCore adversary := by
  unfold SphincsSecurity.gameCore Seeded.gameRest
  change (Seeded.keygen >>= _) = _
  unfold Seeded.keygen gameCore
  simp only [bind_assoc]
  rfl

theorem advantage_embed (adversary : Adversary) :
    SphincsSecurity.forgeAdvantage Seeded.scheme (embed adversary) = forgeAdvantage adversary := by
  rw [advantage_eq_uncounted]
  unfold SphincsSecurity.forgeAdvantage
  rw [game_embed]

end SphincsSecurity.Security
