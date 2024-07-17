import Game.Levels.SetWorld.L05_univ_subset

World "SetWorld"
Level 6

Title "Intersections"

Introduction "The last thing we need to know about subsets is how to work with the intersection
`S ∩ T` of two subsets `S` and `T`. The key lemma you need is
`mem_inter_iff x S T`, which is a proof of `x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T`. That `∧` symbol
means \"and\"."

namespace MySet

lemma mem_inter_iff {𝓧 : Type} (x : 𝓧) (S T : Set 𝓧) : x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by rfl

/--
`mem_inter_iff` is the proof of `∀ x S T, x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T`.

Note that `mem_inter_iff` has three explicit inputs, `x`, `S` and `T`.
-/
TheoremDoc MySet.mem_inter_iff as "mem_inter_iff" in "Set"

NewTheorem MySet.mem_inter_iff

variable (𝓧 : Type)

/-- `S ∩ T = T ∩ S`. -/
TheoremDoc MySet.inter_comm as "inter_comm" in "Set"

/-- `S ∩ T = T ∩ S`. -/
Statement inter_comm (S T : Set 𝓧) : S ∩ T = T ∩ S := by
  Hint (hidden := true) "Start with `ext a`."
  ext a
  Hint (hidden := true) "Now `rw [mem_inter_iff]`"
  rw [mem_inter_iff]
  Hint (hidden := true) "Now do it again!"
  rw [mem_inter_iff]
  Hint (hidden := true) "Split the `↔` with `constructor`."
  constructor
  Hint "This is now tedious because you have to prove the same thing twice. **TODO** refactor? Start with `intro h`"
  intro h
  Hint "Now do `cases' h with h1 h2` to get to the two hypotheses."
  cases' h with h1 h2
  Hint "Now `constructor` and you can finish it."
  constructor
  exact h2
  exact h1
  Hint "This is too tedious -- use `aesop`."
  aesop
