module

public import PaperP1.Model.AllPairExtensionDeficit
public import PaperP1.Model.IndependentDeficitMonotonicity

/-! # The actual all-pair deficit increases with its dyadic subground -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairDeficitMonotonicity

open Finset PaperP1.Model.InfiniteStarts

theorem nonneg (G : Finset ℕ) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ AllPairExtensionDeficit.deficit G L u := by
  apply sum_nonneg
  intro e _
  exact mul_nonneg (abs_nonneg _)
    (IndependentDeficitMonotonicity.nonneg G e (FixedPairExtensions.sourceSpace e L) L u hu)

theorem deficit_mono (G H : Finset ℕ) (hGH : G ⊆ H) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    AllPairExtensionDeficit.deficit G L u ≤ AllPairExtensionDeficit.deficit H L u := by
  calc
    _ ≤ ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| *
        IndependentExtensionDeficit.deficit H e (FixedPairExtensions.sourceSpace e L) L u := by
      apply sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left
        (IndependentDeficitMonotonicity.deficit_mono G H e hGH _ L u hu) (abs_nonneg _)
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨heG, hecard⟩ := mem_powersetCard.mp he
        exact mem_powersetCard.mpr ⟨heG.trans hGH, hecard⟩
      · intro e _ _
        exact mul_nonneg (abs_nonneg _)
          (IndependentDeficitMonotonicity.nonneg H e (FixedPairExtensions.sourceSpace e L) L u hu)

end PaperP1.AllPairDeficitMonotonicity
