import Game.Levels.FilterWorld.L01_univ_mem_principal

World "FilterWorld"
Level 2

Title "Supersets and filters."

Introduction "In this level, we'll show that if `S ∈ 𝓟 A` then any
bigger set `T ⊇ S` is also in `𝓟 A`. Remember that `𝓟 A` is the
collection of all subsets of `𝓧` which contain `A`."

namespace MyGame

variable {𝓧 : Type}

TheoremTab "Filter"

open Filter

/-- If `S ∈ 𝓟 A` and `S ⊆ T` then `T ∈ 𝓟 A`. -/
Statement {A S T : Set 𝓧} (hAS : S ∈ 𝓟 A) (hST : S ⊆ T) : T ∈ 𝓟 A := by
  Hint "Start with `rw [mem_principal] at *` to remove all mention of `𝓟`."
  rw [mem_principal] at *
  Hint "Now you can finish with `exact subset_trans hAS hST`. You can think of `subset_trans` as
  a *function* which takes two proofs as input, and returns another proof as output.
  For example, if you give this functions proofs of `A ⊆ S` and `S ⊆ T`, it will return a proof
  of `A ⊆ T`, which is `exact`ly what we want."
  exact subset_trans hAS hST

Conclusion "Now let's show a fact about `𝓟 A` and intersections."
