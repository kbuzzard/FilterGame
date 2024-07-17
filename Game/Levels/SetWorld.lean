import Game.Levels.SetWorld.L01_subset_refl
import Game.Levels.SetWorld.L02_subset_trans
import Game.Levels.SetWorld.L03_subset_antisymm
import Game.Levels.SetWorld.L04_subset_univ
import Game.Levels.SetWorld.L05_univ_subset
import Game.Levels.SetWorld.L06_inter_comm
import Game.Levels.SetWorld.L07_inter_subset_left
import Game.Levels.SetWorld.L08_subset_inter

World "SetWorld"
Title "Set World"

Introduction "
In this tutorial level we'll learn about sets, subsets, and the intersection of two sets.

Our sets will all be subsets of a fixed \"base set\" `𝓧`.
In particular, whenever we say \"let `S` be a set\" in this level, we mean \"let `S` be a set
of elements of `𝓧`\", and we write `S : Set 𝓧`.

In Lean the base set `𝓧` is called a *type*. If you're used to also thinking of `𝓧` as a set,
this shouldn't cause any problems, but there is one notational difference. Lean uses the notation
`x : 𝓧` to mean that `x` is an element of the base type `𝓧`, but for `S` a set, Lean uses
the notation `x ∈ S` to mean that `x` is an element `S`.

Click \"Start →\" to continue."
