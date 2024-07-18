import Game.Levels.SetWorld.L03_subset_antisymm

World "SetWorld"
Level 4

Title "The \"universal set\""

Introduction "Every set in this world is a subset of `𝓧`, but `𝓧` is a *type*, not a set.
So what is the set which contains every element of `𝓧`? It's called `univ`. And
the axiom you need to know is `mem_univ (x : 𝓧) : x ∈ univ`. You should `apply mem_univ`
when faced with the goal `x ∈ univ`."

namespace MyGame

TheoremTab "Set"

def univ := @Set.univ

lemma mem_univ {𝓧 : Type} (x : 𝓧) : x ∈ univ := by trivial

/--
`mem_univ` is the proof of `∀ x, x ∈ univ`.

When faced with a goal `a ∈ univ`, you can `apply mem_univ` to close it. You can
also do `exact mem_univ a`.
-/
TheoremDoc MyGame.mem_univ as "mem_univ" in "Set"

NewTheorem MyGame.mem_univ

variable {𝓧 : Type}

/-- Any set `S` satisfies `S ⊆ univ`.

More formally, `subset_univ : ∀ (S : Set 𝓧), S ⊆ univ`.-/
TheoremDoc MyGame.subset_univ as "subset_univ" in "Set"

/-- $S ⊆ univ$. -/
Statement subset_univ (S : Set 𝓧) : S ⊆ univ := by
  Hint "Try and the turn the goal into `x ∈ univ` and then `apply mem_univ`."
  rw [subset_def]
  intro x
  intro _hx
  apply mem_univ
