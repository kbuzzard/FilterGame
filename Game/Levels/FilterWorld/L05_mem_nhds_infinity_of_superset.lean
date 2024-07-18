import Game.Levels.FilterWorld.L04_univ_mem_nhds_infinity

World "FilterWorld"
Level 5

Title "The superset axiom for `𝓝∞`."

Introduction "In this level, we'll show that if `S ∈ 𝓝∞` then any
bigger set `T ⊇ S` is also in `𝓝∞`."

namespace MyGame

/--
## Summary

If you have a *hypothesis* `h : ∃ N, blah blah blah` then the hypothesis says
that *some* `N` exists with some property. But you don't *actually have* an `N`
in your variables, just a promise that it exists.

Get that `N` with `cases' h with N hN`.
-/
TacticDoc cases'

NewTactic cases'

open Filter

/-- If `S ∈ 𝓝∞` and `S ⊆ T` then `T ∈ 𝓝∞`. -/
Statement {S T : Set ℕ} (hS : S ∈ 𝓝∞) (hST : S ⊆ T) : T ∈ 𝓝∞ := by
  Hint "Start with `rw [mem_ninf] at *` to remove all mention of `𝓝∞`."
  rw [mem_ninf] at *
  Hint "You now need to get to that `N` whose existence is guaranteed by `hS`. Do
  this with `cases' hS with D hD`"
  cases' hS with D hD
  Hint "I didn't write any more hints yet, but can you do it from here? Tell me where you get stuck
  and I'll put more hints in!"
  use D
  intro i hi
  apply hST
  apply hD
  apply hi

Conclusion "Just `𝓝∞` and intersections left!"
