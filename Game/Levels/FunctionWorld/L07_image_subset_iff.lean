import Game.Levels.FunctionWorld.L06_image_comp

World "FunctionWorld"
Level 7

Title "Function World Final Boss"

Introduction "You've made it to the last level of Function World, congratulations! You've learnt
how to work with
 - preimages,
 - images,
 - and composition of functions.

Importantly you've also learnt how to use the tactics `use` and `cases'`. In this final level
of Function World, we'll equip your toolbox with one last useful tactic `specialize`.

To recap, you might make use of
 - `use` for goals of the form `∃ x, ...`,
 - `intro` for goals of the form `∀ x, ...`,
 - `cases'` for hypotheses of the form `∃ x, ...`.

The tactic `specialize` can be used on hypotheses of the form `∀ x, ...`. Take a look at the
description of `specialize` in the tactics tab on the right.

This level proves a useful theorem that ties together everything you've learnt so far.
Moreover, the proof uses all of the tactics above. Good luck!
"

namespace MyGame

variable {𝓧 𝓨 𝓩: Type}

TheoremTab "Function"

/--
## Summary

The `specialize` tactic can be used to specialize hypotheses that are functions (like `P → Q`)
or universally quanitified statements (like `∀ x, ...`). These are function types; you can think
of them as hypotheses for which you might use `intro` if they were the goal.

The syntax is `specialize <hypothesis> a₁ a₂ ... aₙ` where `a₁ ... aₙ` are the arguments to the
hypothesis to be specialized.

### Example

1. With a hypothesis `h : P → Q` and a proof of `P`, namely `hp: p`, then `specialize h hp`
will replace `h` with the proof of `Q`, that is, you will be left with the hypothesis `h : Q`.

2. With an element `y : 𝓧` and a hypothesis `h : ∀ x, P x` (where `P` is a predicate
`P : 𝓧 → Prop`) then `specialize h y` will replace `h` with `h : P y`.

3. If you have a statement of the form `h : ∃ x ∈ S, P x` for some set `S : Set 𝓧`. Then given an
element `y : 𝓧` and a proof `hy : y ∈ S` you can use `specialize h y hy` to replace `h` with
`h : P y`.

### Notes

Note that after applying `specialize` often `h` is a weaker statement; don't specialize
a hypothesis if you still need the original (stronger) statement later.
-/
TacticDoc specialize
NewTactic specialize


/--
`image_subset_iff` is the proof that...
-/
TheoremDoc MyGame.image_subset_iff as "image_subset_iff" in "Function"

/-- -/
Statement image_subset_iff {S : Set 𝓧} {T : Set 𝓨} {φ : 𝓧 → 𝓨}  : φ '' S ⊆ T ↔ S ⊆ φ ⁻¹' T := by
  Hint "Remember to rewrite with the theorems `subset_def`, `mem_preimage` and `mem_image`
  when appropriate."
  rw [subset_def, subset_def]
  constructor
  . intro h
    intro x hx
    rw [mem_preimage]
    Hint "Here we have a hypothesis of the form `∀ x, ...` so we could use specialize. However,
    a better way to proceed here is to use `apply` (because the goal matches the conclusion of
    the hypothesis)."
    apply h
    rw [mem_image]
    use x
  . intro h
    intro x hx
    rw [mem_image] at hx
    cases' hx with w hw
    cases' hw with hwl hwr
    Hint "This time we have a hypothesis of the form `∀ x, ...` and you will need to use
    `specialize` to continue."
    specialize h w hwl
    rw [mem_preimage, hwr] at h
    exact h

Conclusion "That's enough practice with functions. Going forward, we will be able to use the
concepts of Function World to pull back and push forward filters along functions. The tactics
you've learnt here will also be necessary to be able to prove theorems about more complex
(and important) examples of filters."
