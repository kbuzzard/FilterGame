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

-- Might put these in earlier exercises?
lemma le_self_add {a b : ℕ} : a ≤ a + b := by
  induction b
  rw [Nat.add_zero]
  rw [Nat.add_succ]
  apply Nat.le.step
  exact n_ih

lemma le_add_self {a b : ℕ} : a ≤ b + a := by
  rw [Nat.add_comm]
  apply le_self_add


/--
`le_self_add` is a proof that `a ≤ a + b` for all natural numbers
`a` and `b`.
-/
TheoremDoc MyGame.le_self_add as "le_self_add" in "Nat"

/--
`le_add_self` is similar to `le_self_add` but for `a ≤ b + a`.
-/
TheoremDoc MyGame.le_add_self as "le_add_self" in "Nat"
NewTheorem MyGame.le_self_add MyGame.le_add_self

/-- If `S ∈ 𝓝∞` and `T ∈ 𝓝∞` then `S ∩ T ∈ 𝓝∞`. -/
Statement {S T : Set ℕ} (hS : S ∈ 𝓝∞) (hT : T ∈ 𝓝∞) : S ∩ T ∈ 𝓝∞ := by
  Hint "Start with `rw [mem_ninf] at *` to remove all mention of `𝓝∞`."
  rw [mem_ninf] at *
  Hint "Now `cases' hS with a ha`"
  cases' hS with a ha
  Hint "Now `cases' hT with b hb`"
  cases' hT with b hb
  use a + b
  intro i
  intro h
  rw [mem_inter_iff]
  constructor
  · apply ha
    Hint "Uses `have aq : a ≤ a + b := le_self_add`."
    have aq : a ≤ a + b := le_self_add
    exact Nat.le_trans aq h
  · apply hb
    Hint "Uses `have bq : b ≤ a + b := le_add_self`."
    have bq : b ≤ a + b := le_add_self
    exact Nat.le_trans bq h
  -- -- Original proof
  -- Hint "Start with `rw [mem_ninf] at *` to remove all mention of `𝓝∞`."
  -- rw [mem_ninf] at *
  -- Hint "Now `cases' hS with a ha`"
  -- cases' hS with a ha
  -- Hint "Now `cases' hT with b hb`"
  -- cases' hT with b hb
  -- use max a b
  -- intro i hi
  -- rw [mem_inter_iff]
  -- constructor
  -- ·
  --   specialize ha i
  --   specialize ha ?_
  --   · trans max a b
  --     · exact Nat.le_max_left a b
  --     · exact hi
  --   · apply ha
  -- · specialize hb i ?_
  --   · trans max a b
  --     · exact Nat.le_max_right a b
  --     · exact hi
  --   · exact hb

Conclusion "You just proved the three axioms of a filter."
