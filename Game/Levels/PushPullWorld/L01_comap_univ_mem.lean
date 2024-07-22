import Game.Levels.FunctionWorld
import Game.Levels.FilterWorld

World "PushPullWorld"
Level 1

Title "Pulling back filters."

Introduction "I'll give you the definition of how to pull back a filter. It's then your
job to check the axioms. Let's start with the first one."

namespace MyGame

variable {𝓧 𝓨 : Type} (φ : 𝓧 → 𝓨)

open Filter

TheoremTab "Filter"

variable (𝓖 : Filter 𝓨)

-- axiom mem_comap
lemma mem_comap {A : Set 𝓧} : A ∈ 𝓖.comap φ ↔ ∃ B ∈ 𝓖, φ ⁻¹' B ⊆ A := Iff.rfl

/--
`mem_comap` is the proof that `A ∈ 𝓖.comap φ ↔ ∃ B ∈ 𝓖, φ ⁻¹' B ⊆ A`. This is true
because it's precisely the *definition* of the pullback filter `𝓖.comap φ`.
-/
TheoremDoc MyGame.mem_comap as "mem_comap" in "Filter"

NewTheorem MyGame.mem_comap

/-- `univ` is in the pullback filter. -/
Statement comap_univ_mem : univ ∈ 𝓖.comap φ := by
  sorry

Conclusion "Let's now prove two more basic facts about `𝓟 A`."
