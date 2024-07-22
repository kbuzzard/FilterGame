import Game.Levels.FilterWorld.L04_mem_principal_self

World "FilterWorld"
Level 5

Title "Ordering on filters"

Introduction "The thing you need to remember about filters right now: a filter on `𝓧` is a big
collection of subsets of `𝓧`. They satisfy some axioms, but we don't care about the axioms
right now.

What we care about is the following observation. If `A` is a *small* set, then the filter `𝓟 A`
contains *lots* of sets, because it contains all sets bigger than `A` and `A` is only small.
In contrast, if `A` is a *big* set, there are only a few sets in `𝓟 A`. So the bigger the
set, the fewer sets the filter has in it. This motivates the following *backwards* definition:

If `𝓕` and `𝓖` are filters on `𝓧`, we say `𝓕 ≤ 𝓖` if every subset `S ∈ 𝓖` satisfies `𝓢 ∈ 𝓕`.

The lemma `le_def` says `𝓕 ≤ 𝓖 ↔ ∀ S ∈ 𝓖, S ∈ 𝓕`.

Let's now prove some lemmas about this new `≤` function.

TODO is le_refl too boring or a good start?"

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

lemma le_def {𝓕 𝓖 : Filter 𝓧} : 𝓕 ≤ 𝓖 ↔ ∀ S ∈ 𝓖, S ∈ 𝓕 := by rfl

/--
`le_def` is the definition of `≤` on filters.
-/
TheoremDoc MyGame.le_def as "le_def" in "Filter"

NewTheorem MyGame.le_def

/-- This is the theorem that `𝓕 ≤ 𝓕` for filters. -/
TheoremDoc MyGame.le_refl as "le_refl" in "Filter"

-- TODO needs proof! Also needs hints for new users
/-- `𝓕 ≤ 𝓕`. -/
Statement le_refl (𝓕 : Filter 𝓧) : 𝓕 ≤ 𝓕 := by
  Hint "Start with `rw [le_def]`"
  rw [le_def]
  sorry

Conclusion "Let's now talk about an order on filters."
