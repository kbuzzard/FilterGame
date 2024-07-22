import Game.Levels.FilterWorld.L07_le_antisymm

World "FilterWorld"
Level 8

Title "Principal filters and `≤`."

Introduction "Let's prove a lemma relating `≤` and principal filters."

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- The filter `𝓕` is `≤` the principal filter `A` if and only if `A ∈ 𝓕`. -/
TheoremDoc MyGame.le_principal as "le_principal" in "Filter"

-- **TODO** needs proof
/-- The filter `𝓕` is `≤` the principal filter `A` if and only if `A ∈ 𝓕`. -/
Statement le_principal {𝓕 : Filter 𝓧} {A : Set 𝓧} : 𝓕 ≤ 𝓟 A ↔ A ∈ 𝓕 := by
  sorry

Conclusion "Let's now deduce that `≤` on principal filters agrees with `⊆` on sets."
