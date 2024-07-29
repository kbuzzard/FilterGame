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
sorry
   -- need proof and hints. Start with ext because it's equality of two sets.

Conclusion "There are 6 more levels, all currently explained in the LMSfiltergame.lean file in the repo."
