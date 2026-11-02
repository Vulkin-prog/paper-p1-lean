module

public import PaperP1.Algebra.ElementarySymmetricBound
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Exact pair-product comparison with a literal omitted-pair cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairProductComparison

open Finset PaperP1.SubsetPowerSums

theorem exact_difference {ι : Type*} [DecidableEq ι] (w : ι → ℝ)
    (E : Finset ι) (F : Finset (Finset ι)) (hF : F ⊆ E.powersetCard 2) :
    (∑ e ∈ E, w e) ^ 2 / 2 - (∑ S ∈ F, ∏ e ∈ S, w e) =
      (∑ e ∈ E, w e ^ 2) / 2 + ∑ S ∈ E.powersetCard 2 \ F, ∏ e ∈ S, w e := by
  have hs := square w E
  have hd := sum_sdiff (f := fun S : Finset ι ↦ ∏ e ∈ S, w e) hF
  dsimp only [elementary] at hs
  linarith only [hs, hd]

theorem absolute_bound {ι : Type*} [DecidableEq ι] (w : ι → ℝ)
    (E : Finset ι) (F : Finset (Finset ι)) (hF : F ⊆ E.powersetCard 2) :
    |(∑ e ∈ E, w e) ^ 2 / 2 - (∑ S ∈ F, ∏ e ∈ S, w e)| ≤
      (∑ e ∈ E, w e ^ 2) / 2 + ∑ S ∈ E.powersetCard 2 \ F, ∏ e ∈ S, |w e| := by
  rw [exact_difference w E F hF]
  have hn : 0 ≤ (∑ e ∈ E, w e ^ 2) / 2 := by positivity
  calc
    _ ≤ |(∑ e ∈ E, w e ^ 2) / 2| + |∑ S ∈ E.powersetCard 2 \ F, ∏ e ∈ S, w e| :=
      abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hn]
      apply add_le_add le_rfl
      simpa only [abs_prod] using abs_sum_le_sum_abs
        (fun S : Finset ι ↦ ∏ e ∈ S, w e) (E.powersetCard 2 \ F)

end PaperP1.PairProductComparison
