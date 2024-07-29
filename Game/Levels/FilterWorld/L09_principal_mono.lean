import Game.Levels.FilterWorld.L08_le_principal

World "FilterWorld"
Level 9

Title "Principal filters and `≤`."

Introduction "Let's prove that `≤` on filters \"extends\" `⊆` on sets. In other words,
our definition of `≤` for generalized sets agrees with the usual notion of `⊆` on sets."

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- If `A` and `B` are subsets of `𝓧` then `𝓟 A ≤ 𝓟 B ↔ A ⊆ B` . -/
TheoremDoc MyGame.principal_mono as "principal_mono" in "Filter"

/--  If `A` and `B` are subsets of `𝓧` then `𝓟 A ≤ 𝓟 B ↔ A ⊆ B` . -/
Statement principal_mono {A B : Set 𝓧} : 𝓟 A ≤ 𝓟 B ↔ A ⊆ B := by
constructor
Hint "Try `intro h`"
intro h
apply h
exact mem_principal_self B
Hint "Try `intro h`"
intro h
Hint "use `intro S hS` and see if you can finish it off!"
intro S hS
rw [mem_principal] at *
exact subset_trans h hS

  

Conclusion "The final thing we'll do this in world is to prove that if `𝓟 A = 𝓟 B` then `A = B`.
In other words, we'll show that two distinct sets give us distinct filters."
