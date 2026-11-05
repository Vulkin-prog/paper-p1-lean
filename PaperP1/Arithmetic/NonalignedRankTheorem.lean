module

public import PaperP1.Arithmetic.NonalignedCriticalRank
public import PaperP1.Arithmetic.NonalignedRankLimsup

/-! # Complete main Theorem 13.6 from the actual height-controlled curves

The original finite-pair maximum and literal limsup are retained, including
empty populations and every fixed critical band. No point-count input remains.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedRankTheorem

open Finset Filter FreeComponentRank NonalignedRankLimsup ShortBasisCurveScale

theorem critical_maximal_ratio_bound (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        maximalRatio N L ≤ (2 / 3) * Real.log 2 + ε := by
  classical
  obtain ⟨N₀, hN₀⟩ := NonalignedCriticalRank.critical_rank_bound ε hε C
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

theorem article_13_6 (C : ℝ) (L : ℕ → ℕ)
    (hband : ∀ᶠ N : ℕ in atTop, |(L N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Filter.limsup (fun N ↦ maximalRatio N (L N)) atTop ≤ (2 / 3) * Real.log 2 ∧
      (2 / 3 : ℝ) * Real.log 2 < 1 / 2 := by
  refine ⟨?_, rank_threshold_lt_half⟩
  have hcob := isCoboundedUnder_le_of_le atTop (fun N ↦ maximalRatio_nonneg N (L N))
  rw [← forall_gt_iff_le]
  intro z hz
  obtain ⟨N₀, hN₀⟩ := critical_maximal_ratio_bound
    ((z - (2 / 3) * Real.log 2) / 2) (by linarith) C
  have hevent : ∀ᶠ N : ℕ in atTop,
      maximalRatio N (L N) ≤ (2 / 3) * Real.log 2 + (z - (2 / 3) * Real.log 2) / 2 := by
    filter_upwards [eventually_ge_atTop N₀, hband] with N hN hcrit
    have h := hN₀ N hN (L N) hcrit
    linarith
  exact (limsup_le_of_le hcob hevent).trans_lt (by linarith)

theorem uniform_half_window_gap :
    ∃ σ : ℝ, (2 / 3) * Real.log 2 < σ ∧ σ < 1 / 2 ∧ ∀ C : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → maximalRatio N L ≤ σ := by
  let ε : ℝ := (1 / 2 - (2 / 3) * Real.log 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [rank_threshold_lt_half]
  refine ⟨(2 / 3) * Real.log 2 + ε, by linarith, ?_, ?_⟩
  · dsimp [ε]
    linarith [rank_threshold_lt_half]
  · exact fun C ↦ critical_maximal_ratio_bound ε hε C

end PaperP1.NonalignedRankTheorem
