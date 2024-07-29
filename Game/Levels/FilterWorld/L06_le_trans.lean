import Game.Levels.FilterWorld.L05_le_refl

World "FilterWorld"
Level 6

Title "transitivity of ≤"

Introduction "Let's prove `≤` on filters is transitive."

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- This is the theorem about filters that if `𝓕 ≤ 𝓖` and `𝓖 ≤ 𝓗` then `𝓕 ≤ 𝓗`. -/
TheoremDoc MyGame.le_trans as "le_trans" in "Filter"

/-- If `𝓕 ≤ 𝓖` and `𝓖 ≤ 𝓗` then `𝓕 ≤ 𝓗`. -/
Statement le_trans {𝓕 𝓖 𝓗 : Filter 𝓧} (h1 : 𝓕 ≤ 𝓖) (h2 : 𝓖 ≤ 𝓗) : 𝓕 ≤ 𝓗 := by
  Hint "Start with `rw [le_def] at *`"
  rw [le_def] at *
  Hint "Can you find a way to use `subset_trans`?"
  apply subset_trans h2 h1


Conclusion "You've just proved that `≤` is transitive! Next up we have antisymmetry."
