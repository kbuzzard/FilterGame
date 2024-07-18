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
  Hint "Now `cases' hS with m hm`"
  cases' hS with m hm
  Hint "Now `cases' hT with n hn`"
  cases' hT with n hn
  use max m n
  intro i hi
  rw [mem_inter_iff]
  constructor
  · specialize hm i
    specialize hm ?_
    · trans max m n
      · exact Nat.le_max_left m n -- does exact? work in NNG?
      · exact hi
    · apply hm
  · specialize hn i ?_
    · trans max m n
      · exact Nat.le_max_right m n
      · exact hi
    · exact hn

Conclusion "You just proved the three axioms of a filter."
