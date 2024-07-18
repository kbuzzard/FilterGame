import Game.Levels.SetWorld
import Mathlib.Order.Filter.Basic

World "FilterWorld"
Level 1

Title "The filter associated to a set."

Introduction "Like in Set World, we'll fix a \"base set\" `𝓧`, and all our
sets will be subsets of `𝓧`.

Let `A` be a subset of `𝓧`. Here's the key definition.

Let `𝓟 A` denote the set of *all* the subsets of `𝓧` which contain `A`. In
particular, `𝓟 A` is a *set of sets*. It's called `𝓟` because this
is the *principal filter* associated to `A`.

The name of the key fact you need to know about `𝓟 A`, namely
`S ∈ 𝓟 A ↔ A ⊆ S`, is called `mem_principal`. This is true by definition.

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
  Hint "Now `apply` a theorem we proved already to finish the job."
  apply subset_univ

Conclusion "Let's now prove two more basic facts about `𝓟 A`."
