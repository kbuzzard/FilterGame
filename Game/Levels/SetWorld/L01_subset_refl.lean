import Game.Metadata
import Mathlib.Tactic

World "SetWorld"
Level 1

Title "Sets are subsets of themselves"

Introduction "If `S` and `T` are sets, then `S ⊆ T` means that `S` is a *subset* of `T`.
This means that every element of `S` is also an element of `T`. Let me talk you through
a proof that `S ⊆ S`."

namespace MyGame

TheoremTab "Set"

variable (𝓧 : Type)

/--
## Summary

If `h` is a proof of an implication `X ↔ Y` or an equality `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s. It's the way to \"substitute in\".

### Example:

If your goal is
```
A ⊆ B
```

then

`rw [subset_def]`

will change the goal into `∀ x ∈ A, x ∈ B`.

## Variants

Say `h : X = Y` or `h : X ↔ Y`.

* `rw [← h]` (changes `Y`s to `X`s; get the back arrow by typing `\left ` or `\l`.)

* `rw [h1, h2]` (a sequence of rewrites)

* `rw [h] at h2` (changes `X`s to `Y`s in hypothesis `h2`)

* `rw [h] at h1 h2 ⊢` (changes `X`s to `Y`s in two hypotheses and the goal;
get the `⊢` symbol with `\|-`.)

* `repeat rw [subset_def]` will change all `S ⊆ T`s into their definitions,
until there are no more matches.

* `nth_rewrite 2 [h]` will change only the second `X` in the goal to `Y`.

## Common errors

* You need the square brackets. `rw h` is never correct.

* If `h` is not a *proof* of an *equality* (a statement of the form `X = Y`)
or a *bi-implication* (a statement of the form `X ↔ Y`),
for example if `h` is a function or an implication,
then `rw` is not the tactic you want to use. For example,
`rw [P = Q]` is never correct: `P = Q` is the theorem *statement*,
not the proof. If `h : P = Q` is the proof, then `rw [h]` will work.

## Details

The `rw` tactic is a way to do \"substituting in\". There
are two distinct situations where you can use this tactic.

1) Basic usage: if `h : A = B` is an assumption or
the proof of a theorem, and if the goal contains one or more `A`s, then `rw [h]`
will change them all to `B`'s. The tactic will error
if there are no `A`s in the goal.

2) Advanced usage: Assumptions coming from theorem proofs
often have missing pieces. For example `subset_def`
is really a proof that `?₁ ⊆ ?₂ ↔ ∀ x ∈ ?₁, x ∈ ?₂`,
or, if you like, a proof that `∀ S T, S ⊆ T ↔ ∀ x ∈ S, x ∈ T` because `subset_def` really
is a function, with `S` and `T` the inputs.
In this situation `rw` will look through the goal
for any subterm of the form `?₁ ⊆ ?₂`, and the moment it
finds a match it solves for the `?`s (e.g. `?₁ = A` and `?₂ = B`) and then
then changes all `A ⊆ B`s to `∀ x ∈ A, x ∈ B`s.

If you can't remember the *name* of the proof of an equality or bi-implication, look it up in
the list of lemmas on the right.

-/
TacticDoc rw

/--
## Summary

If the goal is `∀ x, P x`, this mean that you have to prove something for every `x`.
A mathematician might say "Now let `x` be arbitrary". In Lean we say `intro x`.
This will change the goal to `P x`. Note we could equally say `intro fish`,
which would change the goal to `P fish`.

If the goal is `P → Q`, then `intro h` will introduce `h : P` as a hypothesis,
and change the goal to `Q`. Mathematically, it says that to prove $P \implies Q$,
we can assume $P$ and then prove $Q$.

### Example:

If your goal is `∀ x ∈ S, x ∈ T` then `intro a` will give you a new variable `a`
and the goal will become `a ∈ S → a ∈ T`. A second `intro h` will now give you the
hypothesis `h : a ∈ S`, and the goal will change to `a ∈ T`.
-/
TacticDoc intro

/--
## Summary

This tactic has two distinct uses, with two distinct syntaxes:

1) `apply <hypothesis or proof> at <hypothesis>`.
2) `apply <hypothesis or proof>`.

Usage 1) with the `at` is *arguing forwards*. Usage 2 is *arguing backwards*.

Note: `apply h` or `apply h at something` will *only work* if `h` is
a *function*, for example an *implication* `h : P → Q`.

### More explanation

1) If `t : P → Q` is a proof that $P \implies Q$, and `h : P` is a proof of `P`,
then `apply t at h` will change `h` to a proof of `Q`. The idea is that if
you know `P` is true, then you can deduce from `t` that `Q` is true.

2) If your goal is the possible conclusion of a theorem (which might have some
hypotheses), and if `h` is a *proof* of the theorem, then `apply h` will
apply the theorem to the goal. Sometimes it will prove it, and sometimes it
will *reduce* the goal of the level to some simpler goals.

### Examples:

1) (`apply` solving a goal.) `mem_univ` is the proof of the theorem `∀ x : 𝓧, x ∈ univ`. In other words,
`mem_univ` is a *function*, which takes as input a term of type `𝓧` and
returns a proof that `x ∈ univ`.

So if you have `a : X` and your goal is to prove `⊢ a ∈ univ` then `exact mem_univ` will
*not work*, because `mem_univ` has a "for all" in, and the goal does not.
But `apply mem_univ` will work fine, as the `apply` tactic will figure out that
you want to set `x = a`.

2) (`apply` changing a goal.) If your goal is `⊢ A ∪ B = univ` then `apply univ_subset`
will change it to `univ ⊆ A ∪ B`, because `univ_subset` says that for all sets `S`,
`univ ⊆ S` implies `S = univ`. The goal is now slightly logically easier.

3) (`apply ... at` changing a hypothesis.) If you have `h : S ⊆ T` and you
`rw [subset_def] at h`, you'll get `h : ∀ (x : 𝓧), x ∈ S → x ∈ T`. If you
have a second hypothesis `haS : a ∈ S` then `apply h at haS` will turn `haS`
into a now poorly-named proof of `a ∈ T`.

Similarly if `h₁ : log 37 ∈ S` then `apply h at h₁` will give you `h₁ : log 37 ∈ T`.

### Bonus fact if you got to the end

There's something in type theory called "definitional equality" which is part of
the wiring and is not mathematics in the traditional sense. It turns out
that `S ⊆ T` is *definitionally* equal to `∀ (x : 𝓧), x ∈ S → x ∈ T`, so
actually if `h : S ⊆ T` then you can just `apply h` to change `⊢ 42 ∈ T` to
`⊢ 42 ∈ S`. For another example, go back to set world level 1 and try `intro x`
as your first move. What's going on is that the proof of `subset_def` is `rfl`.

-/
TacticDoc apply

/--
## Summary

If the goal is a statement `P`, then `exact h` will close the goal if `h` is a proof of `P`.

### Example

If the goal is `x ∈ S` and you have a hypothesis `h : x ∈ S`
then `exact h` will solve the goal.

### Non-example

If the goal is `x ∈ S`, then `exact x ∈ S` won't work. Exact eats a *proof*
of a mathematical result, not a *statement*.

### Exact needs to be exactly right

`mem_univ` is the theorem that `∀ x : X, x ∈ univ`. In other words, it is a *function*
which takes as input an element of `X` and returns a proof that `x ∈ univ`.

So if you have `a : X` and your goal is `a ∈ univ` then `exact mem_univ` will *not work*,
because `mem_univ` has a "for all" in, and the goal does not. You want
to use `apply mem_univ` in this situation, as the `apply` tactic will figure out
that you want to set `x = a`.

-/
TacticDoc exact

NewTactic rw intro apply exact

/--
`S` is a subset of `T` if and only if every element of `S` is also an element of `T`.
-/
theorem subset_def {𝓧 : Type} {S T : Set 𝓧} : (S ⊆ T) ↔ ∀ x, x ∈ S → x ∈ T := by rfl

/--
`subset_def` is the proof of `(S ⊆ T) ↔ ∀ x, x ∈ S → x ∈ T`.

If you're working with subsets from first principles, then `rw [subset_def]`
will change occurrences of `S ⊆ T` in the goal to `∀ x, x ∈ S → x ∈ T`.

Variants:

* `rw [subset_def] at h` (change the definition at hypothesis `h`)
* `rw [subset_def] at *` (change the definition everywhere)
-/
TheoremDoc MyGame.subset_def as "subset_def" in "Set"

NewTheorem MyGame.subset_def
-- **TODO** warning ``Add `LemmaDoc MyGame.subset_def` somewhere above this statement.``
-- suggests deprecated LemmaDoc

/-- Every set $S$ is a subset of itself. -/
TheoremDoc MyGame.subset_refl as "subset_refl" in "Set"

/-- Every set $S$ is a subset of itself. -/
Statement subset_refl (S : Set 𝓧) : S ⊆ S := by
  Hint "Start with `rw [subset_def]` to replace `S ⊆ S` with its definition."
  rw [subset_def]
  Hint "Now we've got to prove something for all `x`, so `intro x`."
  intro x
  Hint "Now we assume `x ∈ S` with `intro h`."
  intro h
  Hint "And now our goal is exactly `h`, so `exact h` or `apply h` will finish the level."
  apply h

Conclusion "Nice! Let's now prove another basic property of subsets."
