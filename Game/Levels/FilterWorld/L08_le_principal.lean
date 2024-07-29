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

/-- The filter `𝓕` is `≤` the principal filter `A` if and only if `A ∈ 𝓕`. -/
Statement le_principal {𝓕 : Filter 𝓧} {A : Set 𝓧} : 𝓕 ≤ 𝓟 A ↔ A ∈ 𝓕 := by
Hint "Start with `rw [le_def]`"
rw [le_def]
Hint "Do you remember how to split up an iff statement into two cases?"
constructor
Hint "Try `intro h`"
intro h
Hint "Try `specialize h A`"
specialize h A 
Hint "See if you can take it from here!"
apply h
rw[mem_principal]
intro S
intro h
rw[mem_principal]
Hint "Now use `mem_of_superset` and see what you get!"
apply mem_of_superset
exact S

 Conclusion "Let's now deduce that `≤` on principal filters agrees with `⊆` on sets."
