module

public import PaperP1.Analysis.HardSaddleReciprocalUpper
public import PaperP1.Analysis.PrimeProductReciprocalSaddleLower

/-! # All three actual reciprocal sums have coarse hard-saddle order internally -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardSaddleReciprocalBounds

open Finset Filter SaddleParameters SaddleScales HardSaddleGrowth OddPrimePivot
  ReciprocalOddPivots DyadicOddPivots

theorem uniform_sandwich : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    ((N : ℝ) * Real.exp (-10 * saddleCutoff 1 (Real.log N)) ≤ primeSum N ∧
      primeSum N ≤ (N : ℝ) * Real.exp (-saddleCutoff 1 (Real.log N) / 9)) ∧
    ((N : ℝ) * Real.exp (-10 * saddleCutoff 1 (Real.log N)) ≤ pivotSum N ∧
      pivotSum N ≤ (N : ℝ) * Real.exp (-saddleCutoff 1 (Real.log N) / 9)) ∧
    ((N : ℝ) * Real.exp (-11 * saddleCutoff 1 (Real.log N)) ≤ dyadicSum N ∧
      dyadicSum N ≤ (N : ℝ) * Real.exp (-saddleCutoff 1 (Real.log N) / 9)) := by
  obtain ⟨NO, ho⟩ := PrimeProductReciprocalSaddleLower.uniform_ordinary_lower
  obtain ⟨ND, hd⟩ := PrimeProductReciprocalSaddleLower.uniform_dyadic_lower
  obtain ⟨NU, hu⟩ := HardSaddleReciprocalUpper.uniform_upper
  refine ⟨max NO (max ND NU), ?_⟩
  intro N hN
  have hfull : pivotSum N ≤ pivotSum (3 * N) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hl, hh⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨hl, by omega⟩
    · intro _ _ _
      positivity
  have hdyadic : dyadicSum N ≤ pivotSum (3 * N) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hl, hh⟩ := mem_Ico.mp hn
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro _ _ _
      positivity
  have hupper : pivotSum (3 * N) ≤ (N : ℝ) * Real.exp (-saddleCutoff 1 (Real.log N) / 9) := by
    have hh := hu N (by omega)
    linarith only [hh]
  have hordinary := primeSum_le_pivotSum N
  exact ⟨⟨ho N (by omega), hordinary.trans (hfull.trans hupper)⟩,
    ⟨(ho N (by omega)).trans hordinary, hfull.trans hupper⟩,
    ⟨hd N (by omega), hdyadic.trans hupper⟩⟩

theorem log_deficit_bounds {N : ℕ} {S V A : ℝ} (hN : 0 < N) (hV : 0 < V)
    (hl : (N : ℝ) * Real.exp (-A * V) ≤ S)
    (hu : S ≤ (N : ℝ) * Real.exp (-V / 9)) :
    (1 / 9 : ℝ) ≤ (Real.log N - Real.log S) / V ∧ (Real.log N - Real.log S) / V ≤ A := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < S := (mul_pos hn (Real.exp_pos _)).trans_le hl
  have hlow := Real.log_le_log (mul_pos hn (Real.exp_pos _)) hl
  have hhigh := Real.log_le_log hs hu
  rw [Real.log_mul hn.ne' (Real.exp_ne_zero _), Real.log_exp] at hlow hhigh
  exact ⟨(le_div_iff₀ hV).mpr (by linarith only [hhigh]),
    (div_le_iff₀ hV).mpr (by linarith only [hlow])⟩

theorem uniform_normalized_bounds : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    ((1 / 9 : ℝ) ≤ (Real.log N - Real.log (primeSum N)) / saddleCutoff 1 (Real.log N) ∧
      (Real.log N - Real.log (primeSum N)) / saddleCutoff 1 (Real.log N) ≤ 10) ∧
    ((1 / 9 : ℝ) ≤ (Real.log N - Real.log (pivotSum N)) / saddleCutoff 1 (Real.log N) ∧
      (Real.log N - Real.log (pivotSum N)) / saddleCutoff 1 (Real.log N) ≤ 10) ∧
    ((1 / 9 : ℝ) ≤ (Real.log N - Real.log (dyadicSum N)) / saddleCutoff 1 (Real.log N) ∧
      (Real.log N - Real.log (dyadicSum N)) / saddleCutoff 1 (Real.log N) ≤ 11) := by
  obtain ⟨NC, hc⟩ := uniform_sandwich
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop HB))
  refine ⟨max NC NG, ?_⟩
  intro N hN
  have hV := (hb (Real.log N) (hg N (by omega))).2.1
  obtain ⟨hordinary, hfull, hdyadic⟩ := hc N (by omega)
  exact ⟨log_deficit_bounds (by omega : 0 < N) hV hordinary.1 hordinary.2,
    log_deficit_bounds (by omega : 0 < N) hV hfull.1 hfull.2,
    log_deficit_bounds (by omega : 0 < N) hV hdyadic.1 hdyadic.2⟩

end PaperP1.HardSaddleReciprocalBounds
