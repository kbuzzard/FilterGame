import Game.Levels.FilterWorld.L03_inter_mem_principal

World "FilterWorld"
Level 4

Title "`A ∈ 𝓟 A`"

Introduction "Here's another fact about principal filters, which isn't an axiom of a filter
but which might be handy later.

**TODO** needs proof in repo
**TODO** Is this level too boring? Should it be removed"

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- A set `A` is an element of the principal filter `𝓟 A`. -/
TheoremDoc MyGame.mem_principal_self as "mem_principal_self" in "Filter"

-- TODO needs proof! Also needs hints for new users
/-- A set `A` is an element of the principal filter `𝓟 A`. -/
Statement mem_principal_self (A : Set 𝓧) : A ∈ 𝓟 A := by
  sorry



Conclusion "Let's now talk about an order on filters."
