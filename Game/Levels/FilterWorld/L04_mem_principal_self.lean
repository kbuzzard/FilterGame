import Game.Levels.FilterWorld.L03_inter_mem_principal

World "FilterWorld"
Level 4

Title "`A ∈ 𝓟 A`"

Introduction "Here's another fact about principal filters, which isn't
one of the axioms of a filter, but is handy to have around: it's
part of a robust \"API\" for principal filters (i.e., standard lemmas
which are useful to have). See if you can prove it yourself."


namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- A set `A` is an element of the principal filter `𝓟 A`. -/
TheoremDoc MyGame.mem_principal_self as "mem_principal_self" in "Filter"

/-- A set `A` is an element of the principal filter `𝓟 A`. -/
Statement mem_principal_self (A : Set 𝓧) : A ∈ 𝓟 A := by
rw[mem_principal]



Conclusion "Wooah! If you did `rw [mem_principal]` then the goal was closed
automatically! This is because `rw` tries `rfl` afterwards, and `⊆` is reflexive
so `rfl` works and closes the goal completely.

Let's now talk about an order on filters."
