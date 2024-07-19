import Game.Levels.FilterWorld.L06_inter_mem_nhds_infinity

World "FilterWorld"
Level 7

Title "Lemma `𝓟 S = 𝓟 T` implies `S = T`"

Introduction "In this level, we'll show that if `𝓟 S = 𝓟 T` then `S = T`."

open Filter
variable {𝓧 : Type}

Statement {S T : Set 𝓧} (hST : 𝓟 S = 𝓟 T) : S = T := by
  Hint "Start with `have hs : S ∈ 𝓟 S := univ_mem_principal`."
  have hs : S ∈ 𝓟 S := univ_mem_principal
  Hint "Now `have ht : T ∈ 𝓟 T := univ_mem_principal`."
  have ht : T ∈ 𝓟 T := univ_mem_principal
  rw [hST] at hs
  rw [← hST] at ht
  rw [mem_principal] at *
  exact subset_antisymm ht hs

Conclusion "We've shown that if `𝓟 S = 𝓟 T` then `S = T`."
