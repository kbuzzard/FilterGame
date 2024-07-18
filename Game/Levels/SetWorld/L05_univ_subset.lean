import Game.Levels.SetWorld.L04_subset_univ

World "SetWorld"
Level 5

Title "Nothing's bigger than the universal set"

Introduction "See if you can use the tactics we've learnt to prove that if `univ ⊆ S`
then `S = univ`."

namespace MyGame

TheoremTab "Set"

/--
`univ_subset` is the proof that `univ ⊆ S → S = univ`.
-/
TheoremDoc MyGame.univ_subset as "univ_subset" in "Set"

variable {𝓧 : Type}

/-- Any set `S` satisfies `S ⊆ univ`. -/
TheoremDoc MyGame.univ_subset as "univ_subset" in "Set"

/-- If $univ ⊆ S$ then $S = univ$. -/
Statement univ_subset {S : Set 𝓧} (h : univ ⊆ S) : S = univ := by
  Hint (hidden := true) "Try `rw [subset_def] at h`."
  rw [subset_def] at h
  Hint (hidden := true) "Try `ext a`."
  ext a
  Hint (hidden := true) "Try `constructor`."
  constructor
  Hint (hidden := true) "Try `intro h2`"
  intro _h2
  Hint (hidden := true) "Try `apply mem_univ`"
  apply mem_univ
  Hint "Can you finish in one line?"
  Hint (hidden := true) "Try `apply {h}`."
  apply h
