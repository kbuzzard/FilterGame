import Game.Levels.FilterWorld.L09_infinite_inter_filter

World "FilterWorld"
Level 10

Title "Intersection of a principal filter."

Introduction "In this level, we'll see that `∩' (𝓟 S) = S`."

open Filter

variable {𝓧 : Type}

Statement inter_principal_eq_base {S : Set 𝓧} : ∩' (𝓟 S) = S := by
  Hint "Start with `rw [le_antisymm_iff]`."
  rw [le_antisymm_iff]
  refine ⟨?_,?_⟩
  · Hint "Now `have h : S ∈ 𝓟 S := MyGame.univ_mem_principal`."
    have h : S ∈ 𝓟 S := MyGame.univ_mem_principal
    apply inter_le_elem at h
    exact h
  · intro x hx
    intro s hs
    rw [mem_principal] at hs
    exact hs hx


example {S T : Set 𝓧} (hST : 𝓟 S = 𝓟 T) : S = T := by
  have h : ∩' (𝓟 T) = T := inter_principal_eq_base
  rw [← hST] at h
  rw [inter_principal_eq_base] at h
  exact h


Conclusion "Now redo L08 with this new lemma."
