import Game.Levels.SetWorld.L01_subset_refl
import Mathlib.Tactic.ApplyAt

World "SetWorld"
Level 2

Title "Set inclusion is transitive"

Introduction "In this level, we'll show the \"geometrically obvious\"
fact that if `S`, `T` and `U` are sets, with `S ⊆ T`
and `T ⊆ U`, then `S ⊆ U`."

namespace MyGame

TheoremTab "Set"

variable {𝓧 : Type}

/-- If $S ⊆ T$ and $T\subseteq U$ then $S\subseteq U$.
-/
TheoremDoc MyGame.subset_trans as "subset_trans" in "Set"

/-- If $S ⊆ T$ and $T\subseteq U$ then $S\subseteq U$. -/
Statement subset_trans {S T U : Set 𝓧} (hST : S ⊆ T) (hTU : T ⊆ U) : S ⊆ U := by
  Hint "Start with `rw [subset_def] at *` to replace all occurences of the `⊆` symbol with
    their definitions."
  rw [subset_def] at *
  Hint "Now we've got to prove something for all `x`, so `intro x`."
  intro x
  Hint "Now we assume `x ∈ S` with `intro h`"
  intro h
  Hint "Now we just have to put the pieces together.
    You can either argue forwards, with `apply hST at h`,
    or you can argue backwards with `apply hTU`."
  Branch
    apply hST at h
    Hint "Now figure out how to use `hTU` to finish things off."
    Hint (hidden := true) "`apply hTU at h` or `apply hTU` make progress. Then `exact h`"
    apply hTU at h
    exact h
  apply hTU
  Hint "Now figure out how to use `hST` to finish things off."
  Hint (hidden := true) "`apply hST at h` or `apply hST` make progress. Then `exact h`"
  exact hST _ h

Conclusion "Nice! Let's now prove another basic property of subsets."
