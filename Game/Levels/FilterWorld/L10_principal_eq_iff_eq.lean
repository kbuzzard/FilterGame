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
  constructor
  · intro h
    apply subset_antisymm
    · rw [← principal_mono, h]
    · rw [← principal_mono, h]
  · intro h
    rw [h]

Conclusion "Here's my proof:
```
  constructor
  · intro h
    apply subset_antisymm
    · rw [← principal_mono, h]
    · rw [← principal_mono, h]
  · intro h
    rw [h]
```
You don't need to type the dots, they're just to indicate when one goal splits into two.

Congratulations, you've finished the first filter world! If you've already
done function world then you can go on to pushing and pulling filters, apart from the
fact that right now both function world and the pushing/pulling filter world are not
made yet. Check out `https://github.com/kbuzzard/FilterGame/blob/main/Game/LMSfiltergame.lean`
(search for \"# Function World\" and \"# Pushing forward and pulling back filters\") to
see the levels which should go into this world, and feel free to make a pull request
if you want to add some new levels!""
