import Game.Metadata
import Mathlib.Data.Set.Basic

#check Set.subset_def

namespace MySet

/--
`S` is a subset of `T` if and only if every element of `S` is also an element of `T`.
-/
lemma subset_def {𝒳 : Type} {S T : Set 𝒳} : (S ⊆ T) ↔ ∀ x, x ∈ S → x ∈ T := by rfl

end MySet
