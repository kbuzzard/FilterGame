import Game.Levels.SetWorld.L02_subset_trans

World "SetWorld"
Level 3

Title "Set inclusion is antisymmetric"

Introduction "The subset relation `⊆` is a *partial order*. This means that it's reflexive,
transitive, and antisymmetric. In this level we learn two new tactics
to prove that if `S ⊆ T` and `T ⊆ S` then `S = T`."

namespace MyGame

TheoremTab "Set"

/--
## Summary

If the goal is really two goals, for example `P ↔ Q` or `P ∧ Q`, then `constructor`
it into two different goals.

### Example

`constructor` turns the goal `P ↔ Q` into the two goals `P → Q` and `Q → P`.

### Example

`constructor` turns the goal `P ∧ Q` into the two goals `P` and `Q`.
-/
TacticDoc constructor

/--
## Summary

If the goal is the equality of two sets `S = T`, then `ext a` introduces a new variable `a`
and turns the goal into `a ∈ S ↔ a ∈ T`.
-/
TacticDoc ext

NewTactic constructor ext


variable {𝓧 : Type}

/-- If $S ⊆ T$ and $T\subseteq S$ then $S = T$.
-/
TheoremDoc MyGame.subset_antisymm as "subset_antisymm" in "Set"

/-- If $S ⊆ T$ and $T\subseteq S$ then $S = T$. -/
Statement subset_antisymm {S T : Set 𝓧} (hST : S ⊆ T) (hTS : T ⊆ S) : S = T := by
  Hint "We have to prove that two sets are equal. It's an axiom of mathematics
    (\"set extensionality\") that two sets are equal if they have the same elements.
    In Lean the `ext` tactic applies this axiom. Start with `ext a`."
  ext a
  Hint "We now have to prove an if and only if statement `P ↔ Q`, which is the same as proving
  `P → Q` and `Q → P`. Now use the `constructor` tactic to split the goal up into these two goals."
  constructor
  · Hint "This goal is going to follow from the fact that `S ⊆ T`. So let's `rw [subset_def] at hST`
    to get it into a more useful form"
    rw [subset_def] at hST
    Hint "You've seen this kind of goal before in the previous level. See if you can take it from here."
    apply hST
  · apply hTS

Conclusion "Pro tip: you can solve `a ∈ T → a ∈ S` with one tactic `apply hTS`! The reason this works
is that `T ⊆ S` is equal to `∀ x, x ∈ T → x ∈ S` *by definition*, so it is a theorem which
applies for all `x`, and in particular it applies for `x = a`, which is the goal."
