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
-- constructor
-- rw[le_def]
-- intro S
-- apply S
-- apply mem_principal_self
-- rw[le_def]
-- intro h1
-- intro S
-- rw [mem_principal]
-- rw [subset_def]
-- intro h2
rw [le_def]
constructor
· tauto
· intro hA S hAS
  rw [Filter.mem_principal] at hAS
  apply Filter.mem_of_superset hA
  exact hAS





-- Conclusion "Let's now deduce that `≤` on principal filters agrees with `⊆` on sets."
