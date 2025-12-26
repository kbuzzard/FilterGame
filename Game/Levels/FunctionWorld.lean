import Game.Levels.FunctionWorld.L01_preimage_univ
import Game.Levels.FunctionWorld.L02_preimage_inter
import Game.Levels.FunctionWorld.L03_preimage_mono
import Game.Levels.FunctionWorld.L04_image_preimage_subset
import Game.Levels.FunctionWorld.L05_subset_preimage_image
import Game.Levels.FunctionWorld.L06_image_comp
import Game.Levels.FunctionWorld.L07_image_subset_iff

World "FunctionWorld"
Title "Sets and functions"

Introduction "
In world we'll learn about pushing and pulling sets along functions.

Click \"Start →\" to continue."

/-

**TODO**

Future levels (note: stick to mathlib naming convention and implicit input convention 100%)

-- introduce as new axiom
lemma mem_image (φ : 𝓧 → 𝓨) (S : Set 𝓧) (y : 𝓨) : y ∈ φ '' S ↔ ∃ x ∈ S, φ x = y := by rfl

-- function level 4
lemma image_preimage_subset (φ : 𝓧 → 𝓨) (T : Set 𝓨) : φ '' (φ ⁻¹' T) ⊆ T := by

-- function level 5
lemma subset_preimage_image (φ : 𝓧 → 𝓨) (S : Set 𝓧) : S ⊆ φ ⁻¹' (φ '' S) := by

-- function level 6
lemma image_comp (φ : 𝓧 → 𝓨) (ψ : 𝓨 → 𝓩) (S : Set 𝓧) : (ψ ∘ φ) '' S = ψ '' (φ '' S) := by
  aesop -- needs proper proof

-- function level 7/7
lemma image_subset_iff' {S : Set 𝓧} {T : Set 𝓨} {φ : 𝓧 → 𝓨}  : φ '' S ⊆ T ↔ S ⊆ φ ⁻¹' T := by
  rw [subset_def, subset_def]

-/
