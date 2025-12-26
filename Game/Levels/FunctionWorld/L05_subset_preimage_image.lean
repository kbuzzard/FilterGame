import Game.Levels.FunctionWorld.L04_image_preimage_subset
import Mathlib.Order.Filter.Basic

World "FunctionWorld"
Level 5

Title "Images and ⊆"

Introduction "Again we will fix two \"base sets\" `𝓧` and `𝓨` and
a function `φ : 𝓧 → 𝓨`. This time we take a subset of the domain `S : Set 𝓧`
and we prove that `S ⊆ φ⁻¹' ( φ '' S )`.

In this proof you will come across a goal involving the existential quantifier `∃`.
To prove this goal you will need to provide an element that satisfies the quantified
statement. For this you will need the new tactic `use`. Take a look at the description
of `use` in the Tactics tabe on the right."

namespace MyGame

variable {𝓧 𝓨: Type} {φ : 𝓧 → 𝓨} {S : Set 𝓧}

TheoremTab "Function"

/--
## Summary

Use `use <element>` when you need to provide an example element to prove a goal wrapped in
the existential quantifier `∃`.

### Example

* Suppose you have a set `S : Set 𝓧` and an element `x : 𝓧` and a proof that `x` is
contained in `S`, `h : x ∈ S`. If you have a goal `∃ y ∈ S, P y` and a proof that `x`
satisfies the predicate `P`, say `hx: P x`. Then you can prove the goal using `use x`.
Note that `use` intelligently pulls the necessary proofs of `x ∈ S` and `P x` from
the current list of hypotheses.

### Details

Like the `rw` tactic, `use` will attempt to close the goal with `rfl` after
substituting in the given element. So with the hypotheses `x : 𝓧`, `S : Set 𝓧`
and `x ∈ S` and the goal `∃ y ∈ S, y = x`, the tactic `use x` will close the goal
since the subsituted statement `x = x` is proved by `rfl`.
-/
TacticDoc use
NewTactic use


/--
`subset_preimage_image` is the proof that  S ⊆ φ⁻¹' (φ '' S)`.
-/
TheoremDoc MyGame.subset_preimage_image as "subset_preimage_image" in "Function"

/-- The set `S` is a subset of the preimage of its image. -/
Statement subset_preimage_image : S ⊆ φ⁻¹' ( φ '' S ) := by
  Hint "See if you can prove this statement on your own. Remember to use
  the theorems `subset_def`, `mem_preimage` and `mem_image` to turn the goal
  into something more familiar.

  You will need to use the `use` tactic at some point."
  rw [subset_def]
  intro x
  intro h1
  rw [mem_preimage]
  rw [mem_image]
  use x

Conclusion "You've met function preimages and images. Next we shall look at function
composition."
