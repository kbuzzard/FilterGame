import Game.Levels.FilterWorld.L07_principal_le


World "FilterWorld"
Level 8

Title "Equality of principal filters."

Introduction "In this level, we'll show that `𝓟 S = 𝓟 T` implies `S = T`."

open Filter

variable {𝓧 : Type}

Statement {S T : Set 𝓧} (hST : 𝓟 S = 𝓟 T) : S = T := by
  rw [le_antisymm_iff] at hST
  cases' hST with h₁ h₂
  apply principal_le at h₁
  apply principal_le at h₂
  exact subset_antisymm h₁ h₂

Conclusion "We now have one proof of this simple fact and we'll see another proof later with infinite intersection."
