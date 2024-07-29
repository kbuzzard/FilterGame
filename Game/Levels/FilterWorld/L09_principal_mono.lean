import Game.Levels.FilterWorld.L08_le_principal_iff

World "FilterWorld"
Level 9

Title "Principal filters and `≤`."

Introduction "Let's prove that `≤` on filters \"extends\" `⊆` on sets. In other words,
our definition of `≤` for generalized sets agrees with the usual notion of `⊆` on sets.

A hint: you don't have to use `constructor` to solve this level."

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- If `A` and `B` are subsets of `𝓧` then `𝓟 A ≤ 𝓟 B ↔ A ⊆ B` . -/
TheoremDoc MyGame.principal_mono as "principal_mono" in "Filter"

-- **TODO** needs human-readable proof, or explanation of tauto?
/--  If `A` and `B` are subsets of `𝓧` then `𝓟 A ≤ 𝓟 B ↔ A ⊆ B` . -/
Statement principal_mono {A B : Set 𝓧} : 𝓟 A ≤ 𝓟 B ↔ A ⊆ B := by
  rw [le_principal_iff]
  rw [mem_principal]

Conclusion "A two-line proof:
```
  rw [le_principal_iff]
  rw [mem_principal]
```

The goal is closed at the end because it becomes `A ⊆ B ↔ A ⊆ B`, which
can be proved with `rfl` as `↔` is reflexive, and `rw` tries `rfl` after
each usage to see if it works.

The final thing we'll do this in world is to prove that if `𝓟 A = 𝓟 B` then `A = B`.
In other words, we'll show that two distinct sets give us distinct filters."

end MyGame
