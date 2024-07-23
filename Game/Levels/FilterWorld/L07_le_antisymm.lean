import Game.Levels.FilterWorld.L06_le_trans

World "FilterWorld"
Level 7

Title "Antisymmetry of ≤"

Introduction "Let's prove `≤` on filters is antisymmetric."

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- This is the theorem about filters that if `𝓕 ≤ 𝓖` and `𝓖 ≤ 𝓕` then `𝓕 = 𝓖`. -/
TheoremDoc MyGame.le_antisymm as "le_antisymm" in "Filter"

-- TODO needs proof! Also needs hints for new users
/-- If `𝓕 ≤ 𝓖` and `𝓖 ≤ 𝓕` then `𝓕 = 𝓖`. -/
Statement le_antisymm {𝓕 𝓖 : Filter 𝓧} (h1 : 𝓕 ≤ 𝓖) (h2 : 𝓖 ≤ 𝓕) : 𝓕 = 𝓖 := by
  Hint "Two filters are equal if and only if they are the same collection of sets.
  This is an extensionality principle (two things are the same if they're made up of
  the same stuff). So start with `ext S`."
  ext S
  constructor
  Hint "Try using `rw[le_def] at *`"
  rw[le_def] at *
  apply h2
  rw[le_def] at *
  apply h1

Conclusion "Next let's relate `≤` to principal filters."
