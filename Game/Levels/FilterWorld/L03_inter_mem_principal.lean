import Game.Levels.FilterWorld.L02_mem_principal_of_superset

World "FilterWorld"
Level 3

Title "Intersections and filters."

Introduction "In this level, we'll show that if `S ∈ 𝓟 A` and `T ∈ 𝓟 A`
then `S ∩ T ∈ 𝓟 A`."

namespace MyGame

variable {𝓧 : Type}

TheoremTab "Filter"

open Filter

/-- If `S ∈ 𝓟 A` and `T ∈ 𝓟 A` then `S ∩ T ∈ 𝓟 A`. -/
Statement {A S T : Set 𝓧} (hAS : S ∈ 𝓟 A) (hAT : T ∈ 𝓟 A) : S ∩ T ∈ 𝓟 A := by
  Hint "Start with `rw [mem_principal] at *` to remove all mention of `𝓟`."
  rw [mem_principal] at *
  Hint "Now find a relevant theorem to `apply`. You might want to guess the
  name of the theorem before you switch to the `Set` tab to find it.
  Alternatively you can feed the theorem exactly the right inputs and use
  `exact` directly."
  apply subset_inter
  · exact hAS
  · exact hAT

Conclusion "You just proved that `𝓟 A` satisfied the three axioms of a filter."
