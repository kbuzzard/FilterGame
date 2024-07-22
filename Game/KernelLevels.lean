import Game.Levels.FilterWorld
import Mathlib.Order.Filter.Basic

-- Kernel of a filter
-- These should be in first filter world

namespace MyGame

variable {𝓧 : Type}

abbrev mem_ker {𝓕 : Filter 𝓧} {x : 𝓧} :
    x ∈ 𝓕.ker ↔ ∀ A ∈ 𝓕, x ∈ A := Filter.mem_ker -- proof is rfl BTW

/-
What they need to know is the universal property, `mem_ker`.

-/

section sInter_API

variable {𝓕 : Filter 𝓧}

-- It's a lower bound
example : ∀ A ∈ 𝓕, 𝓕.ker ⊆ A := by
  intro S hSP x hx
  simp_rw [mem_ker] at hx
  apply hx
  exact hSP

-- It's the greatest lower bound
example (B : Set 𝓧) (hB : ∀ A ∈ 𝓕, B ⊆ A) :
    B ⊆ 𝓕.ker := by
  intro x hxB S hSP
  apply hB
  apply hSP
  apply hxB

-- experiment
example (B : Set 𝓧) (hB : ∀ A ∈ 𝓕, B ⊆ A) :
    B ⊆ 𝓕.ker := by
  intro x hxB S hSP
  exact hB S hSP hxB

section sInter_levels

-- final boss
open Filter
example (S : Set 𝓧) : (𝓟 S).ker = S := by
  ext x
  rw [Filter.mem_ker] -- not needed in solve_by_elim proof
  constructor -- <;> solve_by_elim --[Filter.mem_ker]
  · -- solve_by_elim works now
    intro h
    apply h
    rw [Filter.mem_principal] -- becomes subset_refl
  · -- solve_by_elim solves this
    intro hxS
    intro A
    intro hAPS
    -- rw [mem_principal] at hAPS
    apply hAPS
    apply hxS

end sInter_levels
