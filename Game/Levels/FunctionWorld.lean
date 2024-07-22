import Game.Levels.FunctionWorld.L01_preimage_univ

World "FunctionWorld"
Title "Sets and functions"

Introduction "
In world we'll learn about pushing and pulling sets along functions.

Click \"Start →\" to continue."

/-

**TODO**

-- function level 2
lemma preimage_inter' {T₁ T₂ : Set 𝓨} :
    φ ⁻¹' (T₁ ∩ T₂) = φ ⁻¹' T₁ ∩ φ ⁻¹' T₂ := by

-- function level 3
lemma preimage_mono' {T₁ T₂ : Set 𝓨} (h : T₁ ⊆ T₂) : φ ⁻¹' T₁ ⊆ φ ⁻¹' T₂ := by

-- introduce as new axiom axiom
lemma mem_image' (S : Set 𝓧) (y : 𝓨) : y ∈ φ '' S ↔ ∃ x ∈ S, φ x = y := by rfl

-- function level 4
lemma image_preimage_subset' (T : Set 𝓨) : φ '' (φ ⁻¹' T) ⊆ T := by

-- function level 5
lemma subset_preimage_image' (S : Set 𝓧) : S ⊆ φ ⁻¹' (φ '' S) := by

-- function level 6
lemma image_comp' (S : Set 𝓧) : (ψ ∘ φ) '' S = ψ '' (φ '' S) := by
  aesop -- needs proper proof

-- function level 7/7
lemma image_subset_iff' (S : Set 𝓧) (T : Set 𝓨) : φ '' S ⊆ T ↔ S ⊆ φ ⁻¹' T := by
  rw [subset_def, subset_def]

-/
