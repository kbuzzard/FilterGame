import Game.Levels.SetWorld

World "FunctionWorld"
Level 1

Title "The preimage of a set under a function."

Introduction "Now we will fix two \"base sets\" `𝓧` and `𝓨`, and let's also
fix a function `φ : 𝓧 → 𝓨`.

In this world we'll learn about pushing forward subsets of `𝓧` along `φ`
to get subsets of `𝓨`, and pulling back subsets of `𝓨`.

This is preparation for pushing forward and pulling back filters, but
we'll get to that later.

Let's start with preimages. If `T` is a subset of `𝓨` then the *preimage* of `T`
along φ is the subset of `𝓧` consisting of all the `x : 𝓧` such that `φ x ∈ T`.

The notation for this in the books is often `φ⁻¹ T`, but in Lean `φ⁻¹` is reserved for
inverses in group theory, so we use `φ ⁻¹'` to do preimages of sets."

namespace MyGame

variable {𝓧 𝓨 : Type} {φ : 𝓧 → 𝓨}

open Filter

TheoremTab "Function"

lemma mem_preimage {T : Set 𝓨} {x : 𝓧} : x ∈ φ ⁻¹' T ↔ φ x ∈ T := by rfl

/--
`mem_preimage` is the proof that `x ∈ φ ⁻¹' T ↔ φ x ∈ T`. This is true
because it's precisely the *definition* of the preimage `φ ⁻¹' T` of `T`.
-/
TheoremDoc MyGame.mem_preimage as "mem_preimage" in "Function"

NewTheorem MyGame.mem_preimage

/-- The preimage of `univ` is `univ`. -/
Statement : φ ⁻¹' univ = univ := by
   Hint "Start in the usual way using `ext` and `constructor` to turn the equality in the goal into two implications."
   ext x
   constructor
   Hint "We can actually prove the first implication without using the definition of a preimage. Can you see how? If you are stuck, take a look back at what we proved in Set World."
   · intro _h
     apply mem_univ
   Hint "For the next part you will have to use `rw [mem_preimage]` to turn the statement `x ∈ φ ⁻¹' univ` into something you can work with. Take a look at the `Function` tab in the `Theorems` panel to see the definition of `mem_preimage`."
   · intro _h
     rw [mem_preimage]
     apply mem_univ

Conclusion "There are 6 more levels, all currently explained in the LMSfiltergame.lean file in the repo."
