import Game.Levels.FilterWorld.L03_inter_mem_principal

World "FilterWorld"
Level 4

Title "Infinitely big numbers."

Introduction "Let's see an example of a filter which isn't principal,
the \"neighbourhoods of infinity\" filter `𝓝∞` on the natural numbers."

namespace MyGame

TheoremTab "Filter"

open Filter

def ninf : Set (Set ℕ) := {S : Set ℕ | ∃ N, ∀ i, N ≤ i → i ∈ S}

notation "𝓝∞" => ninf

lemma mem_ninf {S : Set ℕ} : S ∈ 𝓝∞ ↔ ∃ N, ∀ i, N ≤ i → i ∈ S := by rfl

/--
`mem_ninf` is the proof that `S ∈ 𝓝∞ ↔ ∃ N, ∀ i, N ≤ i → i ∈ S`. This is
true because it's precisely the *definition* of `𝓝∞`.
-/
TheoremDoc MyGame.mem_ninf as "mem_ninf" in "Filter"

NewTheorem MyGame.mem_ninf

/--
## Summary

If the goal is `∃ N, blah blah blah` then to prove such a statement, you
have to show that some `N` exists which makes `blah blah blah` true.
If you think `N = 37` works, then `use 37` will remove the `∃`
and replace all `N`s in `blah blah blah` by 37.

Note: `use` is a dangerous tactic. If you `use` the wrong number,
you can turn a true goal into a false one.

### Example

If the goal is `∃ N, N + N = 4` then `use 2` will turn the
goal into `2 + 2 = 4`, and `use 37` will turn the goal
into `37 + 37 = 4`.

-/
TacticDoc use

NewTactic use

/-- `univ` is an element of `𝓝∞`. -/
Statement : univ ∈ 𝓝∞ := by
  Hint "Start with `rw [mem_ninf]`."
  rw [mem_ninf]
  Hint "To prove an \"exists\" goal we use the `use` tactic. Try `use 37`
  and Lean will replace `N` with `37`."
  use 37
  Hint "Can you take it from here?"
  intro i
  intro _hi
  apply mem_univ

Conclusion "Let's now prove the other two filter axioms for `𝓝∞`."
