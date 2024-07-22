import Mathlib.Tactic
/-!

# Theory of subsets

(partial order, intersection, univ)

-/

--#check Set.subset_refl
--#check Set.subset_rfl
--#check subset_rfl
--#check subset_refl
--#check Set.subset_def

namespace Set

variable (X : Type)

lemma subset_def' (S T : Set X) :
    S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T := by rfl

lemma subset_refl (S : Set X) : S ⊆ S := by
  rw [Set.subset_def']
  intro x
  intro hx
  exact hx

lemma subset_trans {S T U : Set X}
    (hST : S ⊆ T) (hTU : T ⊆ U) : S ⊆ U := by
  rw [Set.subset_def'] at *
  intro x
  intro hu
  apply hST at hu
  apply hTU at hu
  exact hu

lemma subset_antisymm (S T : Set X)
    (hST : S ⊆ T) (hTS : T ⊆ S) : S = T := by
  ext x
  rw [Set.subset_def'] at *
  constructor
  intro hx
  apply hST at hx
  exact hx
  apply hTS
  done

-- tell them it's an axiom
lemma mem_univ' (x : X) : x ∈ univ := by
  trivial

lemma subset_univ' (S : Set X) : S ⊆ univ := by
  rw [Set.subset_def']
  intro x
  intro _hx
  apply mem_univ'

-- tell them it's an axiom
lemma mem_inter' (S T : Set X) (x : X) :
    x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by rfl

lemma inter_subset_left' (S T : Set X) :
    S ∩ T ⊆ S := by
  rw [subset_def']
  intro x
  intro hx
  rw [mem_inter'] at hx
  cases' hx with h1 h2
  exact h1

-- inter_subset_right

lemma subset_inter' {S T U : Set X} (hST : S ⊆ T) (hSU : S ⊆ U) : S ⊆ T ∩ U := by
  rw [subset_def'] at *
  intro x
  intro hx
  rw [mem_inter']
  constructor
  . apply hST at hx
    exact hx
  · apply hSU at hx
    exact hx

/-

## An encoding of subsets.

Let `X` be a type.

What is a topology on `X`? Informally, it is a way
of giving the set some kind of structure, making it
a primitive kind of "geometrical object" or "space".
But formally, it is a collection of subsets of `X`
satisfying some axioms.

Here is an idea, which might seem ridiculous at first: we are going
to "encode" a subset of `X` also as a collection of subsets of `X`
satisfying some axioms.

Concretely, if `A : Set X` is a subset of `X`, let's
"encode" it by studying the collection of all subsets of
`X` which it's contained in. Formally, we will "encode"
`A` with the collection `principal A` of all
`B : Set X` with `A ⊆ B`.

-/

end Set

open Set

-- namespace Filter

-- -- axiom
-- lemma univ_mem'' (F : Filter X) : univ ∈ F := by
--   exact univ_mem

-- -- axiom
-- lemma mem_of_superset' (F : Filter X) (S T : Set X)
--   (hST : S ⊆ T) (hSF : S ∈ F) : T ∈ F := by
--   exact mem_of_superset hSF hST

-- -- axiom
-- lemma inter_mem' (F : Filter X) (S T : Set X)
--     (hSF : S ∈ F) (hTF : T ∈ F) : S ∩ T ∈ F := by
--   exact inter_mem hSF hTF

-- end Filter
-- example: principal filters

section principal

variable {X : Type}

def principal (A : Set X) := {B : Set X | A ⊆ B}

-- axiom
lemma mem_principal {A B : Set X} :
    B ∈ principal A ↔ A ⊆ B := by rfl

variable (A : Set X)

lemma principal_univ_mem : univ ∈ principal A := by
  rw [mem_principal]
  apply subset_univ

lemma principal_mem_of_superset (S T : Set X)
    (hST : S ⊆ T)
    (hS : S ∈ principal A) :
    T ∈ principal A  := by
  rw [mem_principal] at *
  trans S
  · exact hS
  · exact hST

lemma principal_inter_mem (S T : Set X)
    (hS : S ∈ principal A)
    (hT : T ∈ principal A) :
    S ∩ T ∈ principal A := by
  rw [mem_principal] at *
  apply subset_inter hS hT




/-

# All in game up to here

A filter is a collection of subsets satisfying these
three axioms. We've just seen that every set gives a
filter, namely the principal filter.

## Some examples but we need more about inf and sup firtst
-/

end principal

section suff_large

lemma suff_large_univ_mem :
    univ ∈ {B : Set ℕ | ∃ N, ∀ i ≥ N, i ∈ B} := by
  rw [mem_setOf]
  use 37
  intro i _hi
  apply mem_univ

lemma suff_large_mem_of_superset (S T : Set ℕ)
    (hST : S ⊆ T)
    (hS : S ∈ {B : Set ℕ | ∃ N, ∀ i ≥ N, i ∈ B}) :
    T ∈ {B : Set ℕ | ∃ N, ∀ i ≥ N, i ∈ B}  := by
  rw [mem_setOf] at *
  cases' hS with N hS
  use N
  intro j hj
  rw [subset_def] at hST
  specialize hS j hj
  apply hST at hS
  exact hS

lemma suff_large_inter_mem (S T : Set ℕ)
    (hS : S ∈ {B : Set ℕ | ∃ N, ∀ i ≥ N, i ∈ B})
    (hT : T ∈ {B : Set ℕ | ∃ N, ∀ i ≥ N, i ∈ B}) :
    S ∩ T ∈ {B : Set ℕ | ∃ N, ∀ i ≥ N, i ∈ B} := by
  rw [mem_setOf] at *
  cases' hS with N hN
  cases' hT with M hM
  use M ⊔ N
  intro i hi
  rw [mem_inter']
  constructor
  · specialize hN i
    specialize hN ?_
    · trans M ⊔ N
      · exact hi
      · exact Nat.le_max_right M N -- does `exact?` work in actual Filter Game?
    · exact hN
  · specialize hM i ?_
    · trans max M N
      · exact hi
      · exact Nat.le_max_left M N
    · exact hM

end suff_large

section nhds

variable (x : ℝ)

lemma nhds_univ_mem :
    univ ∈ {B : Set ℝ | ∃ ε, 0 < ε ∧ ∀ y, x - ε < y ∧ y < x + ε → y ∈ B} := by
  rw [mem_setOf]
  use 37
  constructor
  · norm_num
  · intro y _hy
    apply mem_univ

lemma nhds_mem_of_superset (S T : Set ℝ)
    (hST : S ⊆ T)
    (hS : S ∈ {B : Set ℝ | ∃ ε, 0 < ε ∧ ∀ y, x - ε < y ∧ y < x + ε → y ∈ B}) :
    T ∈ {B : Set ℝ | ∃ ε, 0 < ε ∧ ∀ y, x - ε < y ∧ y < x + ε → y ∈ B}  := by
  rw [mem_setOf] at *
  cases' hS with ε hS
  cases' hS with hε hS
  use ε
  constructor
  exact hε
  intro y hy
  specialize hS y hy
  rw [Set.subset_def] at hST
  apply hST at hS
  exact hS

lemma nhds_inter_mem (S T : Set ℝ)
    (hS : S ∈ {B : Set ℝ | ∃ ε, 0 < ε ∧ ∀ y, x - ε < y ∧ y < x + ε → y ∈ B})
    (hT : T ∈ {B : Set ℝ | ∃ ε, 0 < ε ∧ ∀ y, x - ε < y ∧ y < x + ε → y ∈ B}) :
    S ∩ T ∈ {B : Set ℝ | ∃ ε, 0 < ε ∧ ∀ y, x - ε < y ∧ y < x + ε → y ∈ B} := by
  rw [mem_setOf] at *
  cases' hS with ε₁ h₁
  cases' h₁ with hε₁ h₁
  cases' hT with ε₂ h₂
  cases' h₂ with hε₂ h₂
  use min ε₁ ε₂
  constructor
  · apply lt_min
    · exact hε₁
    · exact hε₂
  · intro y hy
    rw [mem_inter']
    constructor
    · specialize h₁ y ?_
      · have foo : min ε₁ ε₂ ≤ ε₁
        · exact min_le_left ε₁ ε₂
        constructor <;> linarith
      · exact h₁
    · specialize h₂ y ?_
      · have : min ε₁ ε₂ ≤ ε₂
        · exact min_le_right ε₁ ε₂
        constructor <;> linarith
      · exact h₂

end nhds

namespace Filter

variable (𝓧 : Type)

section order

variable (𝓕 𝓖 : Filter 𝓧)

-- why this way around?
lemma le_def' : 𝓕 ≤ 𝓖 ↔ ∀ S, S ∈ 𝓖 → S ∈ 𝓕 := by rfl

-- because think about principal filters. The smaller the set,
-- the bigger the number of sets which contain it!
-- in fact let's check that that for principal filters
-- ≤ agrees with ⊆ . Let's prove a sublemma first

-- le_refl, trans, antisymm

lemma le_principal (A : Set 𝓧) (𝓕 : Filter 𝓧) : 𝓕 ≤ 𝓟 A ↔ A ∈ 𝓕 := by
  rw [le_def]
  constructor
  · tauto
  · intro hA S hAS
    rw [Filter.mem_principal] at hAS
    apply Filter.mem_of_superset hA
    tauto

-- corollary
lemma principal_le_principal_iff (A B : Set 𝓧) :
    𝓟 A ≤ 𝓟 B ↔ A ⊆ B := by
  rw [le_principal]
  rw [mem_principal]
  -- rfl

end order

end Filter

section functions

/-

Everything so far has gone on within one set X. Let's
now introduce a second subset Y

# Function world
-/

variable (𝓧 𝓨 : Type) (φ : 𝓧 → 𝓨)

namespace Set

-- axiom for preimage of a set
lemma mem_preimage' (T : Set 𝓨) (x : 𝓧) : x ∈ φ ⁻¹' T ↔ φ x ∈ T := by rfl

variable (𝓩 : Type) (ψ : 𝓨 → 𝓩)

-- function level 1
lemma preimage_univ' : φ ⁻¹' univ = univ := by
  ext x
  constructor
  · intro _h
    apply mem_univ
  · intro _h
    rw [mem_preimage]
    apply mem_univ

-- function level 2
lemma preimage_inter' {T₁ T₂ : Set 𝓨} :
    φ ⁻¹' (T₁ ∩ T₂) = φ ⁻¹' T₁ ∩ φ ⁻¹' T₂ := by
  ext x
  rw [mem_preimage]
  rw [mem_inter_iff]
  rw [mem_inter_iff]
  rw [mem_preimage]
  rw [mem_preimage]
  -- rfl

-- function level 3
lemma preimage_mono' {T₁ T₂ : Set 𝓨} (h : T₁ ⊆ T₂) : φ ⁻¹' T₁ ⊆ φ ⁻¹' T₂ := by
  tauto

-- introduce as new axiom axiom
lemma mem_image' (S : Set 𝓧) (y : 𝓨) : y ∈ φ '' S ↔ ∃ x ∈ S, φ x = y := by rfl

-- function level 4
lemma image_preimage_subset' (T : Set 𝓨) : φ '' (φ ⁻¹' T) ⊆ T := by
  intro y
  rintro ⟨x, hx, rfl⟩
  exact hx

-- function level 5
lemma subset_preimage_image' (S : Set 𝓧) : S ⊆ φ ⁻¹' (φ '' S) := by
  intro x hx
  tauto

-- function level 6
example (S : Set 𝓧) : ψ '' (φ '' S) = (ψ ∘ φ) '' S := by
  aesop

-- function level 7/7
example (S : Set 𝓧) (T : Set 𝓨) : φ '' S ⊆ T ↔ S ⊆ φ ⁻¹' T := by
  rw [subset_def, subset_def]
  constructor
  · intro h
    intro x hx
    rw [mem_preimage]
    apply h
    rw [mem_image]
    use x
    -- rfl
  · intro h
    intro y hy
    rw [mem_image] at hy
    cases' hy with x hx
    cases' hx with h1 h2
    specialize h x h1
    rw [mem_preimage] at h
    rw [h2] at h
    exact h

-- Can we do this for filters?
-- This is the big question.

-- Need to be able to pull them back, push them forward,
-- and talk about ≤

end Set

namespace Filter

/-

# Pushing forward and pulling back filters

-/
-- let's try pulling them back first.

section comap
variable (𝓖 : Filter 𝓨)

-- axiom mem_comap
lemma mem_comap''' {A : Set 𝓧} : A ∈ 𝓖.comap φ ↔ ∃ B ∈ 𝓖, φ ⁻¹' B ⊆ A := Iff.rfl

-- level 1
lemma comap_univ_mem : univ ∈ 𝓖.comap φ := by
  rw [mem_comap]
  use univ
  constructor
  · apply Filter.univ_mem
  · rw [subset_def]
    intro x _hx
    apply mem_univ

-- level 2
lemma comap_mem_of_superset (S T : Set 𝓧)
    (hST : S ⊆ T)
    (hS : S ∈ 𝓖.comap φ) :
    T ∈ 𝓖.comap φ := by
  rw [mem_comap] at *
  rcases hS with ⟨B, hBG, hS⟩
  use B
  use hBG
  trans S
  · exact hS
  · exact hST

-- level 3
lemma comap_inter_mem (S T : Set 𝓧)
    (hS : S ∈ 𝓖.comap φ)
    (hT : T ∈ 𝓖.comap φ) :
    S ∩ T ∈ 𝓖.comap φ := by
  rw [mem_comap] at *
  rcases hS with ⟨U, hU1, hU2⟩
  rcases hT with ⟨V, hV1, hV2⟩
  use U ∩ V
  constructor
  · exact inter_mem hU1 hV1
  · rw [subset_def] at *
    intro x hx
    rw [mem_preimage] at hx
    rcases hx with ⟨h1, h2⟩
    apply mem_inter
    · apply hU2
      rw [mem_preimage]
      exact h1
    · apply hV2
      rw [mem_preimage]
      exact h2

-- level 4
lemma comap_principal' (T : Set 𝓨) : 𝓟 (φ ⁻¹' T) = (𝓟 T).comap φ := by
  ext S
  rw [mem_principal, mem_comap]
  tauto

-- level 5
lemma comap_mono' {𝓖₁ 𝓖₂ : Filter 𝓨} (h : 𝓖₁ ≤ 𝓖₂) : 𝓖₁.comap φ ≤ 𝓖₂.comap φ := by
  intro S
  intro hS
  rw [mem_comap] at *
  obtain ⟨T, hT, hTS⟩ := hS
  tauto

end comap

section map

variable (𝓕 : Filter 𝓧)

-- level 5
lemma map_univ_mem : univ ∈ 𝓕.map φ := by
  rw [mem_map]
  rw [preimage_univ]
  apply univ_mem

-- level 6
lemma map_mem_of_superset (S T : Set 𝓨)
    (hST : S ⊆ T)
    (hS : S ∈ 𝓕.map φ) :
    T ∈ 𝓕.map φ := by
  rw [mem_map] at *
  apply mem_of_superset hS
  rw [subset_def] at *
  intro y hy
  rw [mem_preimage] at *
  apply hST
  exact hy

-- level 7
lemma map_inter_mem (S T : Set 𝓨)
    (hS : S ∈ 𝓕.map φ)
    (hT : T ∈ 𝓕.map φ) :
    S ∩ T ∈ 𝓕.map φ := by
  rw [mem_map] at *
  rw [preimage_inter]
  apply inter_mem
  · exact hS
  · exact hT

-- level 8
lemma map_principal' (S : Set 𝓧) : 𝓟 (φ '' S) = (𝓟 S).map φ := by
  ext T
  rw [mem_principal, mem_map, mem_principal]
  constructor <;> simp

-- level 9
lemma map_mono' {𝓕₁ 𝓕₂ : Filter 𝓧} (h : 𝓕₁ ≤ 𝓕₂) : 𝓕₁.map φ ≤ 𝓕₂.map φ := by
  intro S
  intro hS
  rw [mem_map] at *
  tauto

-- level 10 (boss)
lemma map_le_iff_le_comap' (𝓕 : Filter 𝓧) (𝓖 : Filter 𝓨) : 𝓕.map φ ≤ 𝓖 ↔ 𝓕 ≤ 𝓖.comap φ := by
  constructor
  · intro h
    intro S
    rw [mem_comap]
    intro h
    obtain ⟨T, hT, hTS⟩ := h
    refine Filter.mem_of_superset ?_ hTS
    apply h -- pro move
    exact hT
  · intro h S hSG
    rw [mem_map]
    apply h
    rw [mem_comap]
    tauto

-- def
lemma tendsto_def' (𝓖 : Filter 𝓨) : 𝓕.Tendsto φ 𝓖 ↔ 𝓕.map φ ≤ 𝓖 := by rfl

lemma tendsto_iff_comap' (𝓖 : Filter 𝓨) : 𝓕.Tendsto φ 𝓖 ↔ 𝓕 ≤ 𝓖.comap φ := by
  rw [tendsto_def']
  rw [map_le_iff_le_comap']

-- level 11 boss

variable {𝓩 : Type} (ψ : 𝓨 → 𝓩)

lemma Tendsto.comp' (𝓖 : Filter 𝓨) (𝓗 : Filter 𝓩) (h1 : 𝓕.Tendsto φ 𝓖) (h2 : 𝓖.Tendsto ψ 𝓗) : 𝓕.Tendsto (ψ ∘ φ) 𝓗 := by
  rw [tendsto_def'] at *
  trans map ψ 𝓖

  apply map_mono


  sorry
end map
