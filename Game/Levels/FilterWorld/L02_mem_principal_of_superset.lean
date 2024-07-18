import Game.Levels.FilterWorld.L01_univ_mem_principal

World "FilterWorld"
Level 2

Title "Supersets and filters."

Introduction "In this level, we'll show that if `S ∈ 𝓟 A` then any
bigger set `T ⊇ S` is also in `𝓟 A`."

namespace MyGame

variable {𝓧 : Type}

TheoremTab "Filter"

open Filter

/-- If `S ∈ 𝓟 A` and `S ⊆ T` then `T ∈ 𝓟 A`. -/
Statement {A S T : Set 𝓧} (hAS : S ∈ 𝓟 A) (hST : S ⊆ T) : T ∈ 𝓟 A := by
  Hint "Start with `rw [mem_principal] at *` to remove all mention of `𝓟`."
  rw [mem_principal] at *
  Hint "Now you can finish with `exact subset_trans hAS hST`"
  exact subset_trans hAS hST

Conclusion "Now let's show a fact about `𝓟 A` and intersections."
