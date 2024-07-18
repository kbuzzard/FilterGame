import Game.Levels.SetWorld.L05_univ_subset

World "SetWorld"

Level 6

Title "Intersections"

Introduction "The last thing we need to know about subsets is how to work with the intersection
`S ∩ T` of two subsets `S` and `T`. The key lemma you need is
`mem_inter_iff x S T`, which is a proof of `x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T`. That `∧` symbol
means \"and\"."

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

lemma mem_inter_iff {𝓧 : Type} (x : 𝓧) (S T : Set 𝓧) : x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by rfl

/--
`mem_inter_iff` is the proof of `∀ x S T, x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T`.

Note that `mem_inter_iff` has three explicit inputs, `x`, `S` and `T`.
-/
TheoremDoc MyGame.mem_inter_iff as "mem_inter_iff" in "Set"

NewTheorem MyGame.mem_inter_iff

variable (𝓧 : Type)

/-- `S ∩ T = T ∩ S`. -/
TheoremDoc MyGame.inter_comm as "inter_comm" in "Set"

/-- `S ∩ T = T ∩ S`. -/
Statement inter_comm (S T : Set 𝓧) : S ∩ T = T ∩ S := by
  Hint "Start with `ext a`."
  ext a
  Hint "We are trying to get this goal into a form where the `tauto` tactic
  will solve it. Click on the `tauto` tactic on the right to see what
  it does. Then try `rw [mem_inter_iff]`"
  rw [mem_inter_iff]
  Hint "Now do it again, and the goal will be purely a logic goal."
  rw [mem_inter_iff]
  Hint "This has now got nothing to do with sets. Prove this logic goal with `tauto`."
  tauto
