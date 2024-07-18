import Mathlib.Tactic
/-!

# Theory of subsets

(partial order, intersection, univ)

-/

variable (X : Type)

--#check Set.subset_refl
--#check Set.subset_rfl
--#check subset_rfl
--#check subset_refl
--#check Set.subset_def

namespace Set

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

def principal {X : Type} (A : Set X) := {B : Set X | A ⊆ B}

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

A filter is a collection of subsets satisfying these
three axioms. We've just seen that every set gives a
filter, namely the principal filter.

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
  use max M N
  intro i hi
  rw [mem_inter']
  constructor
  · specialize hN i
    specialize hN ?_
    · trans max M N
      · exact hi
      · exact Nat.le_max_right M N -- does exact? work in NNG?
    · exact hN
  · specialize hM i ?_
    · trans max M N
      · exact hi
      · exact Nat.le_max_left M N
    · exact hM

-- theorem: this is not principal.
-- Indeed given any A, can find a set in P(A) but not in ... meh
-- ⊥ and ⊤ are principal so this proof might be messy.

-- this would be useful
lemma foo (A : Set X) (x : X) : x ∈ A ↔ ∀ B ∈ principal A, x ∈ B := by
  constructor
  · intro hA B
    rw [mem_principal]
    intro hAB
    rw [subset_def] at hAB
    apply hAB
    exact hA
  · intro h
    specialize h A
    apply h
    rw [mem_principal]
    -- rfl

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

section order

variable (F G : Filter X)

-- why this way around?
lemma le_def' : F ≤ G ↔ ∀ S, S ∈ G → S ∈ F := by rfl

-- because think about principal filters. The smaller the set,
-- the bigger the number of sets which contain it!
-- in fact let's check that that for principal filters
-- ≤ agrees with ⊆ . Let's prove a sublemma first


lemma le_principal (A : Set X) (F : Filter X) : F ≤ 𝓟 A ↔ A ∈ F := by
  rw [le_def]
  simp_rw [Filter.mem_principal]
  constructor
  · intro h
    apply h
    apply Set.subset_refl
  · intro h B hAB
    apply Filter.mem_of_superset h hAB

-- corollary
lemma principal_le_principal_iff (A B : Set X) :
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

-/

variable (X Y : Type) (f : X → Y)

example (S : Set X) : Set Y := f '' S

namespace Set

lemma mem_image' (S : Set X) (y : Y) : y ∈ f '' S ↔ ∃ x ∈ S, f x = y := by rfl

lemma mem_preimage' (T : Set Y) (x : X) : x ∈ f ⁻¹' T ↔ f x ∈ T := by rfl

variable (Z : Type) (g : Y → Z)

-- sublemma
lemma preimage_univ' : f ⁻¹' univ = univ := by
  ext x
  constructor
  · intro _h
    apply mem_univ
  · intro _h
    rw [mem_preimage]
    apply mem_univ

lemma preimage_inter' {T₁ T₂ : Set Y} :
    f ⁻¹' (T₁ ∩ T₂) = f ⁻¹' T₁ ∩ f ⁻¹' T₂ := by
  ext x
  rw [mem_preimage]
  rw [mem_inter_iff]
  rw [mem_inter_iff]
  rw [mem_preimage]
  rw [mem_preimage]
  -- rfl

-- sublemma

-- example (U : Set Z) : f ⁻¹' (g ⁻¹' U) = (g ∘ f) ⁻¹' U := by
--   ext x
--   rw [mem_preimage]
--   rw [mem_preimage]
--   rw [mem_preimage]
--   rw [Function.comp_apply]
--   -- rfl

-- example (S : Set X) : g '' (f '' S) = (g ∘ f) '' S := by
--   ext z
--   rw [mem_image]
--   rw [mem_image]
--   simp_rw [mem_image]
--   -- bleurgh
--   sorry

-- tendsto for sets
example (S : Set X) (T : Set Y) : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
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

-- let's try pulling them back first.

section comap
variable (G : Filter Y)

lemma comap_univ_mem : univ ∈ {A | ∃ B ∈ G, f ⁻¹' B ⊆ A} := by
  rw [mem_setOf]
  use univ
  constructor
  · apply Filter.univ_mem
  · rw [subset_def]
    intro x _hx
    apply mem_univ

lemma comap_mem_of_superset (S T : Set X)
    (hST : S ⊆ T)
    (hS : S ∈ {A | ∃ B ∈ G, f ⁻¹' B ⊆ A}) :
    T ∈ {A | ∃ B ∈ G, f ⁻¹' B ⊆ A} := by
  rw [mem_setOf] at *
  rcases hS with ⟨B, hBG, hS⟩
  use B
  use hBG
  trans S
  · exact hS
  · exact hST

lemma comap_inter_mem (S T : Set X)
    (hS : S ∈ {A | ∃ B ∈ G, f ⁻¹' B ⊆ A})
    (hT : T ∈ {A | ∃ B ∈ G, f ⁻¹' B ⊆ A}) :
    S ∩ T ∈ {A | ∃ B ∈ G, f ⁻¹' B ⊆ A} := by
  rw [mem_setOf] at *
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

end comap

section map

variable (F : Filter X)

lemma map_univ_mem : univ ∈ {B | f ⁻¹' B ∈ F} := by
  rw [mem_setOf]
  rw [preimage_univ]
  apply univ_mem

lemma map_mem_of_superset (S T : Set Y)
    (hST : S ⊆ T)
    (hS : S ∈ {B | f ⁻¹' B ∈ F}) :
    T ∈ {B | f ⁻¹' B ∈ F} := by
  rw [mem_setOf] at *
  apply mem_of_superset hS
  rw [subset_def] at *
  intro y hy
  rw [mem_preimage] at *
  apply hST
  exact hy

lemma map_inter_mem (S T : Set Y)
    (hS : S ∈ {B | f ⁻¹' B ∈ F})
    (hT : T ∈ {B | f ⁻¹' B ∈ F}) :
    S ∩ T ∈ {B | f ⁻¹' B ∈ F} := by
  rw [mem_setOf] at *
  rw [preimage_inter]
  apply inter_mem
  · exact hS
  · exact hT

end map
