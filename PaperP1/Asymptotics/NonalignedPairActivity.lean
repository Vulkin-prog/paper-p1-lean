module

public import PaperP1.Asymptotics.WeightedNonalignedPairs
public import PaperP1.Model.NonalignedActivityHostCap

/-! # The full actual nonaligned pair activity has unconditional exponent -1+epsilon -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedPairActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NonalignedActivityHostCap

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) ≤
        (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NW, _hNW, hw⟩ := WeightedNonalignedPairs.uniform_families C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨2 + NW + NG, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hcover := ActivityFamilyCover.two_families L (AllAlignedPairs.nonaligned N L)
    ((sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ))) ∅
    (fun _ he hn ↦ mem_union_left _ (nonzero_cover (by omega) hL he hn))
  simp only [CompatibleActivitySplit.absolute, sum_empty, add_zero] at hcover
  calc
    _ ≤ ∑ e ∈ (sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ)),
        |infiniteCenteredCoefficient L e| := hcover
    _ ≤ ∑ p ∈ sources N L, |infiniteCenteredCoefficient L {p.1, p.2}| :=
      sum_image_le_of_nonneg (f := fun e : Finset ℕ ↦ |infiniteCenteredCoefficient L e|)
        (fun _ _ ↦ abs_nonneg _)
    _ ≤ _ := (hw N (by omega) L hband (sources N L)
      (fun _ hp ↦ mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1)
      (fun _ hp ↦ (mem_filter.mp hp).2.1.ne)
      (fun _ hp ↦ (mem_filter.mp hp).2.2)).2

end PaperP1.NonalignedPairActivity
