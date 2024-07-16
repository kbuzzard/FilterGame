import Game.Metadata
import Game.MySet.Lemmas
World "SetWorld"
Level 1

Title "Sets are subsets of themselves"

Introduction "If `S` and `T` are sets, then `S ⊆ T` means that `S` is a *subset* of `T`.
This means that every element of `S` is also an element of `T`. Let me talk you through
a proof that `S ⊆ S`."

namespace MySet

variable (𝓧 : Type)

/-- **TODO** -/
TacticDoc rw

/-- **TODO** -/
TacticDoc intro

/-- **TODO** -/
TacticDoc apply

/-- **TODO** -/
TacticDoc exact

NewTactic rw intro apply exact

/--
`subset_def` is the proof of `(S ⊆ T) ↔ ∀ x, x ∈ S → x ∈ T`.

If you're working with subsets from first principles, then `rw [subset_def]`
will change occurrences of `S ⊆ T` in the goal to `∀ x, x ∈ S → x ∈ T`.

Variants:

* `rw [subset_def] at h` (change the definition at hypothesis `h`)
* `rw [subset_def] at *` (change the definition everywhere)
-/
TheoremDoc MySet.subset_def as "subset_def" in "Set"

NewTheorem MySet.subset_def
-- **TODO** warning ``Add `LemmaDoc MySet.subset_def` somewhere above this statement.``
-- suggests deprecated LemmaDoc

/-- Every set $S$ is a subset of itself. -/
TheoremDoc MySet.subset_refl as "subset_refl" in "Set"

/-- Every set $S$ is a subset of itself. -/
Statement subset_refl (S : Set 𝓧) : S ⊆ S := by
  Hint "Start with `rw [subset_def]` to replace `S ⊆ S` with its definition."
  rw [subset_def]
  Hint "Now we've got to prove something for all `x`, so `intro x`."
  intro x
  Hint "Now we assume `x ∈ S` with `intro h`"
  intro h
  Hint "And now our goal is exactly `h`, so `exact h` or `apply h` will finish the level."
  apply h

Conclusion "Nice! Let's now prove another basic property of subsets."
