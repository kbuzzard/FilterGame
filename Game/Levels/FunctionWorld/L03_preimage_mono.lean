import Game.Levels.FunctionWorld.L02_preimage_inter

World "FunctionWorld"
Level 3

Title "Preimages and `⊆`."

Introduction "Given two sets `T₁` and `T₂` with `T₁ ⊆ T₂` then we know that `φ ⁻¹' T₁ ⊆ φ ⁻¹' T₂`. Let's prove this!"

namespace MyGame

variable {𝓧 𝓨 : Type} {φ : 𝓧 → 𝓨} {T₁ T₂ : Set 𝓨}

open Filter

/--
`preimage_mono` is the proof that given `T₁ ⊆ T₂` for two sets `T₁` and `T₂` we have `φ ⁻¹' T₁ ⊆ φ ⁻¹' T₂`.
-/
TheoremDoc MyGame.preimage_mono as "preimage_mono" in "Function"

/-- Given `T₁ ⊆ T₂` we have `φ ⁻¹' T₁ ⊆ φ ⁻¹' T₂`.-/
Statement preimage_mono (h : T₁ ⊆ T₂)  : φ ⁻¹' T₁ ⊆ φ ⁻¹' T₂  := by
  Hint "Start with `rw [subset_def]`."
  rw [subset_def]
  Hint "Now use `intro x` to work with the quantified statement."
  intro x
  Hint "Now you can take it from here. You will need to rewrite the preimages using `mem_preimage`."
  rw [mem_preimage, mem_preimage]
  intro p
  apply h at p
  exact p

Conclusion "The last three levels have involved a fair bit of repetitive work: we've been doing a lot of rewriting definitions or proving statements you can obviously see to be true. Lean has a solution to this tedium, namely the tactic `tauto`. It is designed to solve goals that are logical tautologies but it also does quite a bit of work in unpacking definitions. See the Tactics tab for more.

It turns out the last three levels can be solved by `tauto` alone! Don't believe it? Go back and give it a try.

Next we will look at the image of a set and consider a theorem on the image of a preimage.
"
