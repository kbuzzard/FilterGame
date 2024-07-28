import Game.Levels.SetWorld
import Mathlib.Order.Filter.Basic

World "FilterWorld"
Level 1

Title "The filter associated to a set."

Introduction "Like in Set World, we'll fix a \"base set\" `𝓧`, and all our
sets will be subsets of `𝓧`.

Before I give you the *definition* of a filter, I will give you an *example*.

Let `A` be a subset of `𝓧`. We are going to define the *principal filter*
associated to `A`. It is a *set of subsets* of `𝓧`, called `𝓟 A`.
A subset `S` is in `𝓟 A` if and only if `A ⊆ S`.

The name of this key fact `S ∈ 𝓟 A ↔ A ⊆ S` is `mem_principal`.

In the first three levels of this game, we'll prove three easy facts
about `𝓟 A` using `mem_principal`. The first one is about the set
`univ` whose elements are all of `𝓧`. "

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

lemma mem_principal {A S : Set 𝓧} : S ∈ 𝓟 A ↔ A ⊆ S := by rfl

/--
`mem_principal` is the proof that `S ∈ 𝓟 A ↔ A ⊆ S`. This is true
because it's precisely the *definition* of `𝓟 A`.
-/
TheoremDoc MyGame.mem_principal as "mem_principal" in "Filter"

NewTheorem MyGame.mem_principal

/-- `univ` is an element of `𝓟 A`. -/
Statement (A : Set 𝓧) : univ ∈ 𝓟 A := by
  Hint "Start with `rw [mem_principal]`."
  rw [mem_principal]
  Hint "Now `apply` a theorem we proved already to finish the job. Take a look at the `Set` tab
  in the `Theorems` panel on the right to remind yourself of the theorems we've proved about sets."
  apply subset_univ

Conclusion "Let's now prove two more basic facts about `𝓟 A`."
