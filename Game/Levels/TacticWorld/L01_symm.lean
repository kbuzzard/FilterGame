import Game.Metadata
import Mathlib.Tactic

World "TacticWorld"
Level 1

Title "The `symm` tactic."

-- What the user sees when they start the level
Introduction "The `symm` tactic is easy to use and understand.
It changes goals of the form `⊢ X = Y` to `⊢ Y = X`. Here `X`
and `Y` can be numbers or sets or filters or anything.

It also changes goals of the form `⊢ P ↔ Q` to `⊢ Q ↔ P`. You can
also make it work on hypotheses (for example `h : X = Y`), with `symm at h`.

Why don't you try a simple example."

/-- If $x$ and $y$ are real numbers and $x = y$, then $y = x$. -/
Statement (x y : ℝ) (h : x = y) : y = x := by
  Hint "You can finish this using `rw`. But can you find a `rw`-free proof using `symm` and `exact`?
  Try using `symm` on either the goal or `h`."
  symm
  exact h

-- What the user sees when they finish the level
Conclusion "Nice! You've now unlocked the `symm` tactic."

-- Documentation which the user sees when they click on the tactic.
/--
## Summary

The `symm` tactic turns goals of the form `⊢ X = Y` to `⊢ Y = X`,
and goals of the form `⊢ P ↔ Q` to `⊢ Q ↔ P`. You can use `symm at h`
to make it work on hypotheses `h : X = Y` too.

### Example

If the goal is `⊢ 2 + 2 = 4` and you try `symm`, the goal
will become `⊢ 4 = 2 + 2`.

### Example

If `h : S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T` then `symm at h` will change `h`
into `(∀ x, x ∈ S → X ∈ T) ↔ S ⊆ T`.
-/
TacticDoc symm

-- Makes `symm` appear on the list of tactics.
NewTactic symm
