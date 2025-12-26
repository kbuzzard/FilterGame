import Game.Levels.FunctionWorld.L03_preimage_mono
import Mathlib.Order.Filter.Basic

World "FunctionWorld"
Level 4

Title "Images and ⊆"

Introduction "Again we will fix two \"base sets\" `𝓧` and `𝓨` and
a function `φ : 𝓧 → 𝓨`.

Now we can discuss images. Is `S` is a subset of `𝓧` then the
*image* of `S` along `φ` is the subset of `𝓨` consisting of all the
`y : 𝓨` such that there exists an `x : 𝓧` with `φ x = y`.

The notation for this in textbooks is often `φ S`, but in Lean this is reserved
for function application, so we use `φ '' S` to denote the images of sets.

Take a look at the new theorem `mem_image` (in the Functions tab). This theorem
encapsulates the definition above.

Because the use of the existential quantifier `∃`, we will need the help of a new tactic
`cases'`. Take a look at description of `cases'` in the list of tactics on the right.
In particular, we will use `cases'` to instantiate an element from a hypothesis written
with `∃`."

namespace MyGame

variable {𝓧 𝓨: Type} {φ : 𝓧 → 𝓨} {T : Set 𝓨}

TheoremTab "Function"

/--
## Summary

The `cases'` tactic can be used to \"split up\" hypotheses. For example, when working with a
hypothesis containing logical AND statement or a existential quantifier:

* If we have a hypothesis `h: P x ∧ Q x` then `cases' h with hl hr` will turn `h` into two new
hypotheses `hl : P x` and `hr : Q x`. In this case, `hl` is the name we have given to the left
hand side of the logical AND statement and `hr` the name given to the right hand side.

* If we have a hypothesis `h : ∃ x, P x` where `P x` is a statement depending on `x : 𝓧`. Then
the tactic `cases' h with x hx` will turn this into two hypotheses, `x : 𝓧` and `hx : P x`.
Note that when we quanitify a variable over a set, such as in the statement `∃ x ∈ S, P x`,
this is really just shorthand for `∃ x, x ∈ S ∧ P x`.

### Example

* Suppose we have sets `S : Set 𝓧`, `T : Set 𝓧` and the hypothesis `h: ∃ y ∈ S, y ∈ T`. Then we
can use the
tactic `cases' h with w hw` to \"split up\" `h` into the variable `w : 𝓧` and the hypothesis
`hw : w ∈ S ∧ w ∈ T`. We could have renamed the quantified variable `y` anything. Here we have
renamed it `w` in the new hypotheses.

### Notes

If you have played the Natural Numbers Game then you will have come across this tactic
before under the name `cases` (without the apostrophe). Thie change of name came about with the
migration to Lean 4. Lean 4 introduced a new `cases` tactic, saving the old tactic with the
name `cases'`. For Filter Game, we will use the older `cases'` as it has the simpler syntax
(and Natural Numbers Game players will be familiar it).
-/
TacticDoc cases'
NewTactic cases'


lemma mem_image (φ : 𝓧 → 𝓨) (S : Set 𝓧) (y : 𝓨) : y ∈ φ '' S ↔ ∃ x ∈ S, φ x = y := by rfl
/--
`mem_image` is the proof that `y ∈  φ '' S ↔ ∃ x ∈ S, φ x = y`. This is true
because it's precisely the *definition* of the image `φ '' S` of `S`.
-/
TheoremDoc MyGame.mem_image as "mem_image" in "Function"
NewTheorem MyGame.mem_image


/--
`image_preimage_subset` is the proof that  φ '' (φ⁻¹' T) ⊆ T`.
-/
TheoremDoc MyGame.image_preimage_subset as "image_preimage_subset" in "Function"

/-- The image of a preimage of a set `T` is a subset of `T`. -/
Statement image_preimage_subset : φ '' (φ⁻¹' T) ⊆ T := by
  Hint "In order to get used to the new tactic, we will walk you through proving this theorem which
  describe how sets behave under images of preimages.

  Start with `rw [subset_def]` and `intro x`.
  Then use `intro h` to introduce the hypothesis `h`."
  rw [subset_def]
  intro x
  intro h
  Hint "Now we have a hypothesis that deals with the image of a set. Use `rw [mem_image] at h` to
  turn this into something more familiar."
  rw [mem_image] at h
  Hint "The hypothesis `h` is written with the existential quanitfier `∃`. See if you can use
  the `cases'` tactic to instantiate a variable satisfying the property specified by `h`.
  Remember, you can look at the examples in the description of `cases'` in the
  tactics panel on the right."
  cases' h with w hw
  Hint "Now use `cases'` again to break up the logical AND statement into its left and right
  component parts."
  cases' hw with hwl hwr
  Hint "Great! Now see if you can finish off the level. Remember to use the `mem_preimage` theorem."
  rw [mem_preimage, hwr] at hwl
  exact hwl
