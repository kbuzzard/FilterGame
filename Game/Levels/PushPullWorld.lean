import Game.Levels.FunctionWorld
import Game.Levels.FilterWorld

World "PushPullWorld"
Title "Pushing and pulling filters along functions"

Introduction "
In world we'll learn about pushing and pulling *filters* along functions.

Click \"Start →\" to continue."

/-
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

-- level 6
lemma map_univ_mem : univ ∈ 𝓕.map φ := by
  rw [mem_map]
  rw [preimage_univ]
  apply univ_mem

-- level 7
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

-- level 8
lemma map_inter_mem (S T : Set 𝓨)
    (hS : S ∈ 𝓕.map φ)
    (hT : T ∈ 𝓕.map φ) :
    S ∩ T ∈ 𝓕.map φ := by
  rw [mem_map] at *
  rw [preimage_inter]
  apply inter_mem
  · exact hS
  · exact hT

-- level 9
lemma map_principal' (S : Set 𝓧) : 𝓟 (φ '' S) = (𝓟 S).map φ := by
  ext T
  rw [mem_principal, mem_map, mem_principal]
  constructor <;> simp

-- level 10
lemma map_mono' {𝓕₁ 𝓕₂ : Filter 𝓧} (h : 𝓕₁ ≤ 𝓕₂) : 𝓕₁.map φ ≤ 𝓕₂.map φ := by
  intro S
  intro hS
  rw [mem_map] at *
  tauto

variable {𝓩 : Type} (ψ : 𝓨 → 𝓩)

-- level 11
lemma map_comp {𝓕 : Filter 𝓧} : 𝓕.map (ψ ∘ φ) = (𝓕.map φ).map ψ := by
  ext S
  rw [mem_map]
  rw [mem_map]
  rw [mem_map]
  rw [iff_iff_eq]
  rfl -- don't tell anyone

-- level 12 (final boss)
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

-/
