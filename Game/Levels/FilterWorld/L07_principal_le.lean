import Game.Levels.FilterWorld.L06_inter_mem_nhds_infinity

World "FilterWorld"
Level 7

Title "`𝓟 S ≤ 𝓟 T`."

Introduction "In this level, we'll show that if `𝓟 S ≤ 𝓟 T` then `S ⊆ T`"

open Filter
variable {𝓧 : Type}

/--
`principal_le` is the proof of `(𝓟 S ≤ 𝓟 T) → S ⊆ T`.
-/
TheoremDoc MyGame.principal_le as "principal_le" in "Filter"

Statement principal_le {S T : Set 𝓧} (hST : 𝓟 S ≤ 𝓟 T) : S ⊆ T := by
  Hint "Start with `rw [le_def] at hST`."
  rw [le_def] at hST
  rw [← mem_principal]
  apply hST
  rw [mem_principal]

Conclusion "We now have an ordering for filters."
