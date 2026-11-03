module

public import PaperP1.Model.IndependentExtensionDeficit

/-! # Independent deficits increase with their actual target ground -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentDeficitMonotonicity

open Finset PaperP1.Arithmetic PaperP1.Model.InfiniteStarts

theorem nonneg (G S : Finset ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ)
    (u : ℝ) (hu : 0 ≤ u) : 0 ≤ IndependentExtensionDeficit.deficit G S W L u := by
  exact sum_nonneg fun A _ ↦ mul_nonneg (pow_nonneg hu _)
    (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)

theorem families_mono (G H : Finset ℕ) (hGH : G ⊆ H)
    (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) :
    IndependentExtensionDeficit.families G W L ⊆ IndependentExtensionDeficit.families H W L := by
  intro A hA
  obtain ⟨hAG, hn⟩ := (IndependentExtensionDeficit.mem_families G W L A).mp hA
  exact (IndependentExtensionDeficit.mem_families H W L A).mpr ⟨hAG.trans hGH, hn⟩

theorem deficit_mono (G H S : Finset ℕ) (hGH : G ⊆ H)
    (W : Submodule F₂ (ℕ →₀ F₂)) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    IndependentExtensionDeficit.deficit G S W L u ≤ IndependentExtensionDeficit.deficit H S W L u := by
  apply sum_le_sum_of_subset_of_nonneg
  · apply families_mono
    intro x hx
    obtain ⟨hxG, hxS⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hGH hxG, hxS⟩
  · intro A _ _
    exact mul_nonneg (pow_nonneg hu _)
      (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)

end PaperP1.IndependentDeficitMonotonicity
