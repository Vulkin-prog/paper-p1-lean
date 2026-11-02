module

public import PaperP1.Arithmetic.NonalignedRankUnderBCN
public import Mathlib.Order.LiminfLimsup

/-! # The actual finite-pair maximum and the source nonaligned limsup

The maximum is set to zero when there are no nonaligned pairs. Every asymptotic
conclusion retains the ordinary explicit integer-polynomial BCN input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedRankLimsup

open Finset Filter PaperP1.FreeComponentRank PaperP1.NonalignedRankUnderBCN
  PaperP1.ShortBasisCurveScale

def nonalignedPairs (N L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((PaperP1.Model.dyadicBlock N) ×ˢ (PaperP1.Model.dyadicBlock N)).filter
    (fun p ↦ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L)

def maximalRank (N L : ℕ) : ℕ :=
  (nonalignedPairs N L).sup (fun p ↦ pairIntersectionRank p.1 p.2 L)

def maximalRatio (N L : ℕ) : ℝ := (maximalRank N L : ℝ) / ((L + 1 : ℕ) : ℝ)

theorem maximalRatio_nonneg (N L : ℕ) : 0 ≤ maximalRatio N L := by
  unfold maximalRatio
  positivity

theorem pair_ratio_le_maximal (N L x y : ℕ) (hx : x ∈ PaperP1.Model.dyadicBlock N)
    (hy : y ∈ PaperP1.Model.dyadicBlock N) (hnon : ¬ CompressedTargetAlignment.Aligned 1 x y L) :
    (pairIntersectionRank x y L : ℝ) / ((L + 1 : ℕ) : ℝ) ≤ maximalRatio N L := by
  classical
  have hmem : (x, y) ∈ nonalignedPairs N L := by
    simp only [nonalignedPairs, mem_filter, mem_product]
    exact ⟨⟨hx, hy⟩, hnon⟩
  have h := Finset.le_sup (f := fun p ↦ pairIntersectionRank p.1 p.2 L) hmem
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h

theorem critical_maximal_ratio_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : IntegerCurvePointInput.UniformBound c κ) (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        maximalRatio N L ≤ (2 / 3) * Real.log 2 + ε := by
  classical
  obtain ⟨N₀, hN₀⟩ := critical_rank_bound c κ hc hBCN ε hε C
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  by_cases hne : (nonalignedPairs N L).Nonempty
  · obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup (nonalignedPairs N L) hne
      (fun p ↦ pairIntersectionRank p.1 p.2 L)
    obtain ⟨hprod, hnon⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hprod
    unfold maximalRatio maximalRank
    rw [heq]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < ((L + 1 : ℕ) : ℝ))).mpr
      (hN₀ N hN L hband p.1 hx p.2 hy hnon)
  · have hempty : nonalignedPairs N L = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [maximalRatio, maximalRank, hempty, sup_empty]
    rw [Nat.bot_eq_zero, Nat.cast_zero, zero_div]
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity

theorem article_13_6_under_BCN (c κ : ℝ) (hc : 0 < c)
    (hBCN : IntegerCurvePointInput.UniformBound c κ) (C : ℝ) (L : ℕ → ℕ)
    (hband : ∀ᶠ N : ℕ in atTop, |(L N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Filter.limsup (fun N ↦ maximalRatio N (L N)) atTop ≤ (2 / 3) * Real.log 2 ∧
      (2 / 3 : ℝ) * Real.log 2 < 1 / 2 := by
  refine ⟨?_, rank_threshold_lt_half⟩
  have hcob := isCoboundedUnder_le_of_le atTop (fun N ↦ maximalRatio_nonneg N (L N))
  rw [← forall_gt_iff_le]
  intro z hz
  obtain ⟨N₀, hN₀⟩ := critical_maximal_ratio_bound c κ hc hBCN
    ((z - (2 / 3) * Real.log 2) / 2) (by linarith) C
  have hevent : ∀ᶠ N : ℕ in atTop,
      maximalRatio N (L N) ≤ (2 / 3) * Real.log 2 + (z - (2 / 3) * Real.log 2) / 2 := by
    filter_upwards [eventually_ge_atTop N₀, hband] with N hN hcrit
    have h := hN₀ N hN (L N) hcrit
    linarith
  exact (limsup_le_of_le hcob hevent).trans_lt (by linarith)

theorem uniform_half_window_gap (c κ : ℝ) (hc : 0 < c)
    (hBCN : IntegerCurvePointInput.UniformBound c κ) :
    ∃ σ : ℝ, (2 / 3) * Real.log 2 < σ ∧ σ < 1 / 2 ∧ ∀ C : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → maximalRatio N L ≤ σ := by
  let ε : ℝ := (1 / 2 - (2 / 3) * Real.log 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [rank_threshold_lt_half]
  refine ⟨(2 / 3) * Real.log 2 + ε, by linarith, ?_, ?_⟩
  · dsimp [ε]
    linarith [rank_threshold_lt_half]
  · exact fun C ↦ critical_maximal_ratio_bound c κ hc hBCN ε hε C

end PaperP1.NonalignedRankLimsup
