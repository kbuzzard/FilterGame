import Game.Levels.SetWorld.L06_inter_comm

World "SetWorld"

Level 7

Title "`S ∩ T ⊆ S`"

Introduction "Let's prove `inter_subset_left`, the statement that `S ∩ T ⊆ S`."

/--
## Summary

If the goal is a true statement in pure logic, like `P → (Q → P)` or `P ∧ Q → Q ∧ P`
(where `P` and `Q` can represent any mathematical true/false statements) then
the `tauto` tactic will solve it.
-/
TacticDoc tauto

NewTactic tauto

namespace MyGame

TheoremTab "Set"

variable (𝓧 : Type)

/-- `S ∩ T ⊆ S`. -/
TheoremDoc MyGame.inter_subset_left as "inter_subset_left" in "Set"

/-- `S ∩ T ⊆ S`. -/
Statement inter_subset_left (S T : Set 𝓧) : S ∩ T ⊆ S := by
  Hint "There's a subtlety here, so let me talk you through it. Start of course with
    `rw [subset_def]`."
  rw [subset_def]
  Hint "Now you can see `x ∈ S ∩ T` in the goal, but `rw [mem_inter_iff]` will *fail*, because
  \"`rw` doesn't work under binders\". In other words, that `x` isn't a variable yet,
  it's a \"for all `x`\". Make it a variable with `intro x`."
  intro x
  Hint "Now you have an actual `x : 𝓧` in your list of variables, so `rw [mem_inter_iff]` will
    work."
  rw [mem_inter_iff]
  Hint "Now finish this pure logic goal in one line."
  tauto
