import Game.Levels.FunctionWorld.L01_preimage_univ

World "FunctionWorld"
Level 2

Title "The preimage of a set under a function."

Introduction "In this level we shall prove that preimages preserve intersections.
That is, for a function `φ : 𝓧 → 𝓨` and sets `T₁,T₂` in `𝓨` we have
`φ ⁻¹' (T₁ ∩ T₂) = φ ⁻¹' T₁ ∩ φ ⁻¹' T₂`."

namespace MyGame

variable {𝓧 𝓨 : Type} {φ : 𝓧 → 𝓨} {T₁ T₂ : Set 𝓨}

open Filter

/--
`preimage_inter` is the proof that `φ ⁻¹' (T₁ ∩ T₂) = φ ⁻¹' T₁ ∩ φ ⁻¹' T₂`.
-/
TheoremDoc MyGame.preimage_inter as "preimage_inter" in "Function"

/-- The preimage of an intersection is the intersection of preimages i.e. `φ ⁻¹' (T₁ ∩ T₂) = φ ⁻¹' T₁ ∩ φ ⁻¹' T₂`. -/
Statement preimage_inter: φ ⁻¹' (T₁ ∩ T₂) = φ ⁻¹' T₁ ∩ φ ⁻¹' T₂ := by
  Hint "We need to prove an equality of sets, so start with `ext`."
  ext
  Hint "It is possible to continue using the `constructor` tactic as we have done before. Instead, see if you can find a shorter proof using `rw` statements and the theorems on intersections."
  rw [mem_inter_iff]
  rw [mem_preimage, mem_preimage, mem_preimage]
  rw [mem_inter_iff]

Conclusion "Note that if you used `rw` as the last tatic, it will have closed the goal. This is because `rw` will always try to finish a proof with `rfl` after performing any rewriting.

Next we shall look at how preimages interact with `⊆`."
