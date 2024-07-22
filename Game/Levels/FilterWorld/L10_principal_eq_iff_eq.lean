import Game.Levels.FilterWorld.L09_principal_mono

World "FilterWorld"
Level 10

Title "`principal_eq_iff_eq`."

Introduction "Let's prove that `≤` on filters \"extends\" `⊆` on sets. In other words,
our definition of `≤` for generalized sets agrees with the usual notion of `⊆` on sets."

namespace MyGame

variable {𝓧 : Type}

open Filter

TheoremTab "Filter"

/-- If `A` and `B` are subsets of `𝓧` then `𝓟 A ≤ 𝓟 B ↔ A ⊆ B`. -/
TheoremDoc MyGame.principal_mono as "principal_mono" in "Filter"

-- **TODO** needs human-readable proof, or explanation of tauto?
/--  If `A` and `B` are subsets of `𝓧` then `𝓟 A = 𝓟 B ↔ A = B`. -/
Statement principal_eq_iff_eq {A B : Set 𝓧} : 𝓟 A = 𝓟 B ↔ A = B := by
  sorry -- use antisymm and previous level and ext and hopefully that's it

Conclusion "Congratulations, you've finished the first filter world! If you've already
done function world then you can go on to pushing and pulling filters."
