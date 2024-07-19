-- This level is WIP until
-- I define the docstrings of a bunch more tactics
-- and possibly write some new levels which explain how to use `max` and `min`

import Game.Levels.FilterWorld.L05_mem_nhds_infinity_of_superset

World "FilterWorld"
Level 6

Title "Intersection axiom for `𝓝∞`."

Introduction "In this level, we'll show that if `S ∈ 𝓝∞` and `T ∈ 𝓝∞`
then `S ∩ T ∈ 𝓝∞`."

namespace MyGame

open Filter

/-- If `S ∈ 𝓝∞` and `T ∈ 𝓝∞` then `S ∩ T ∈ 𝓝∞`. -/
Statement {S T : Set ℕ} (hS : S ∈ 𝓝∞) (hT : T ∈ 𝓝∞) : S ∩ T ∈ 𝓝∞ := by
  Hint "Start with `rw [mem_ninf] at *` to remove all mention of `𝓝∞`."
  rw [mem_ninf] at *
  Hint "Now `cases' hS with a ha`"
  cases' hS with a ha
  Hint "Now `cases' hT with b hb`"
  cases' hT with b hb
  use max a b
  intro i hi
  rw [mem_inter_iff]
  constructor
  ·
    specialize ha i
    specialize ha ?_
    · trans max a b
      · exact Nat.le_max_left a b
      · exact hi
    · apply ha
  · specialize hb i ?_
    · trans max a b
      · exact Nat.le_max_right a b
      · exact hi
    · exact hb

Conclusion "You just proved the three axioms of a filter."
