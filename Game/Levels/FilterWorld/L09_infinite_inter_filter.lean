import Game.Levels.FilterWorld.L08_principal_eq

World "FilterWorld"
Level 9

Title "Infinite intersection of filter."

Introduction "In this level, we'll see the definition and some properties of the infinite intersection of a filter."

def inter (f : Filter α) : Set α := { a | ∀ s ∈ f, a ∈ s }
notation "∩'" => inter

variable {𝓧 : Type}

Statement inter_le_elem {f : Filter 𝓧} : ∀ s ∈ f, ∩' f ⊆ s := by
  Hint "Start with `intro s hs`."
  intro s hs
  Hint "Then `intro x hx`."
  intro x hx
  Hint "Now `apply hx at hs`."
  apply hx at hs
  exact hs

Conclusion "We have now seen that the intersection of the elements of a filter is a subset of any element in the filter."
