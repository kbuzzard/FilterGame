import Game.Levels.FunctionWorld.L05_subset_preimage_image

World "FunctionWorld"
Level 6

Title "Function Composition"

Introduction "This level works with function composition. In Lean we can denote
function composition with the `∘` symbol (typed using \\circ). Take a look
at the new theorem `comp_def` in the Theorems tab which gives the definition
of function composition.

This level is quite tricky and will make repeated use of the `cases'` and `use`
tactics."

namespace MyGame

variable {𝓧 𝓨 𝓩: Type} {φ : 𝓧 → 𝓨} {ψ : 𝓨 → 𝓩}

TheoremTab "Function"

lemma comp_def (x : 𝓧): (ψ ∘ φ) x = ψ (φ x) := by rfl

/--
`comp_def` is the proof that `(ψ ∘ φ) x = ψ (φ x) `. This is true because
it's precisely the *definition* of the composition of functions. -/
TheoremDoc MyGame.comp_def as "comp_def" in "Function"
NewTheorem MyGame.comp_def

/--
  `image_comp` is the proof that `(ψ ∘ φ) '' S = ψ '' (φ '' S)`.
-/
TheoremDoc MyGame.image_comp as "image_comp" in "Function"

/-- `(ψ ∘ φ) '' S = ψ '' (φ '' S)` -/
Statement image_comp (S : Set 𝓧) : (ψ ∘ φ) '' S = ψ '' (φ '' S) := by
  Hint "Start with `ext` and `constuctor`."
  ext
  constructor
  Hint "Introduce the hypthosis `h` with `intro h`."
  . intro h
    Hint "Try `rw [mem_image] at *` to simplify statements concerning images of sets."
    rw [mem_image] at *
    Hint "Now we have a hypothesis stating the existence of a element of `S` that maps
     to `x` under the composition `ψ ∘ φ`. Use `cases' h with s hs` to create such an element."
    cases' h with s hs
    Hint "The hypothesis `hs` now comprises of a logical AND statement. Use `cases'` again
    to break this up into the left and right parts."
    cases' hs with hsl hsr
    Hint "Now we need to prove the existence of an element of `φ '' S`. So apply the `use`
    tactic with a suitable choice. Note that `use s` won't work as `s` is not an element of
    `φ '' S`."
    use (φ s)
    Hint "Great! Now use prove the goal by splitting it up with `constructor`. If the first
    subgoal seems a bit obvious, try proving it using `tauto`. For the second subgoal remember
    that you can use `comp_def`."
    constructor
    . tauto
    . rw [comp_def] at hsr
      exact hsr

  Hint "Excellent work! We're half way to proving the theorem. Start by introducing the hypothesis
  with `intro h` and then rewrite things with `rw [mem_image] at *`, just like before."
  . intro h
    rw [mem_image] at *
    Hint "Just like before, we have a hypothesis stating the existence of an element of `S`
    satisfying a certain property. Use `cases'` repeatedly to break apart this hypothesis."
    cases' h with y hy
    cases' hy with hyl hyr
    Hint "Keep rewriting with `mem_image` and using `cases'` to break apart existence hypotheses."
    rw [mem_image] at hyl
    cases' hyl with w hw
    cases' hw with hwl hwr
    Hint "Great! Now select a candidate to prove the goal with the `use` tactic."
    use w
    Hint "Now try and finish the proof. Remember you can use `comp_def` to rewrite expressions
    containing the `∘` symbol."
    constructor
    . exact hwl
    . rw [comp_def]
      rw [hwr, hyr]
