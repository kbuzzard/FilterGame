import Game.Levels.FilterWorld.L07_le_antisymm

World "FilterWorld"
Level 8

Title "Principal filters and `≤`."

Introduction "Let's prove a lemma relating `≤` and principal filters.
To do this one, you'll need to know one of the axioms of a filter,
which is that if `A ∈ 𝓕` and `A ⊆ B` then `B ∈ 𝓕`. This is
called `mem_of_superset`; take a look at its documentation to see
how to use it."

namespace MyGame

variable {𝓧 : Type}

open Filter
#check mem_of_superset

lemma mem_of_superset {𝓕 : Filter 𝓧} {A B : Set 𝓧} (hA : A ∈ 𝓕)
    (hAB : A ⊆ B) : B ∈ 𝓕 := Filter.mem_of_superset hA hAB

/--
`mem_of_superset` is the proof of the axiom for filters which
says that `A ∈ 𝓕` and `A ⊆ B` implies `B ∈ 𝓕`.

If you have a goal `B ∈ 𝓕` and you attempt to `apply mem_of_superset`
then things will get a bit confusing, because Lean will not know
what you want `A` to be. If you have a proof `hA : A ∈ 𝓕` to hand
then `apply mem_of_superset hA` will work, and will turn the
goal into `A ⊆ B`. Alternatively, if you have a proof `hAB : A ⊆ B`
to hand, then you can `apply mem_of_superset _ hAB` and Lean will
leave you with the `_` goal, which is `A ∈ 𝓕`.

Finally, if you have both `hA : A ∈ 𝓕` and `hAB : A ⊆ B` then
`exact mem_of_superset hA hAB` will close the goal `B ∈ 𝓕` for you
immediately.
-/
TheoremDoc MyGame.mem_of_superset as "mem_of_superset" in "Filter"

NewTheorem MyGame.mem_of_superset

TheoremTab "Filter"

/-- The filter `𝓕` is `≤` the principal filter `𝓟 A` if and only if `A ∈ 𝓕`. -/
TheoremDoc MyGame.le_principal as "le_principal" in "Filter"

/-- The filter `𝓕` is `≤` the principal filter `A` if and only if `A ∈ 𝓕`. -/
Statement le_principal {𝓕 : Filter 𝓧} {A : Set 𝓧} : 𝓕 ≤ 𝓟 A ↔ A ∈ 𝓕 := by
Hint "Start with `rw [le_def]`"
rw [le_def]
Hint "Do you remember how to split up an iff statement into two cases?"
constructor
· Hint "Try `intro h`"
  intro h
  Hint "You can now `apply {h}`."
  apply h
  Hint "See if you can take it from here!"
  rw [mem_principal]
· intro h
  intro S
  rw [mem_principal]
  Hint "Here you can just `apply mem_of_superset`!"
  apply mem_of_superset
  exact h

 Conclusion "Let's now deduce that `≤` on principal filters agrees with `⊆` on sets."
