module

public import PaperP1.Analysis.ReciprocalOddPivotDyadicScale
public import PaperP1.Analysis.SaddlePowerErrors

/-! # The actual reciprocal-pivot ledger at three times the original height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalOddPivotTripleScale

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.ReciprocalOddPivots
  PaperP1.OrdinaryReciprocalPrimeInput PaperP1.ReciprocalOddPivotFullScale
  PaperP1.ReciprocalOddPivotDyadicScale

theorem upper_with_one (hinput : EIPInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      pivotSum (3 * N) + 1 ≤ 4 * (N : ℝ) *
        Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  obtain ⟨NF, hF⟩ := uniform_full_sandwich hinput (ε / 2) (by positivity)
  obtain ⟨NP, hP⟩ := SaddlePowerErrors.power_negligible 1 0 0 1 (by norm_num) (by norm_num)
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hG⟩ := eventually_atTop.mp
    (hnlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (max (Real.log 3) 1))))
  refine ⟨max NF (max NP NG), ?_⟩
  intro N hN
  have hnr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdom := hG N (by omega)
  have hroot : saddleThreshold 1 ≤ Real.log N := (le_max_left _ _).trans hdom
  have hH : 0 < Real.log N := by
    have hh := (le_max_right _ _).trans ((le_max_right _ _).trans hdom)
    linarith
  have h3 : Real.log 3 ≤ Real.log N := (le_max_left _ _).trans ((le_max_right _ _).trans hdom)
  have hnu : 0 ≤ saddleNu 1 (Real.log N) :=
    (div_pos hH (saddleCutoff_pos (by norm_num) hroot)).le
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hmono := SaddleMonotonicity.cutoff_monotone (by norm_num : (0 : ℝ) < 1)
    hroot (show Real.log N ≤ Real.log N + Real.log 3 by linarith)
  have hnu3 := nu_shift_bound hroot hH hlog3 h3
  have htriple : Real.log ((3 * N : ℕ) : ℝ) = Real.log N + Real.log 3 := by
    push_cast
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnr.ne']
    ring
  have hfull := (hF (3 * N) (by omega)).2
  rw [htriple] at hfull
  have hexp : -2 * saddleCutoff 1 (Real.log N + Real.log 3) +
      (ε / 2) * saddleNu 1 (Real.log N + Real.log 3) ≤
      -2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N) := by
    have hh := mul_le_mul_of_nonneg_left hnu3 (by positivity : 0 ≤ ε / 2)
    linarith only [hmono, hh]
  have hu := hfull.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (by positivity : (0 : ℝ) ≤ ((3 * N : ℕ) : ℝ)))
  push_cast at hu
  have hp := hP N (by omega)
  simp only [Real.rpow_zero, Real.rpow_one, one_mul, zero_mul, sub_zero] at hp
  have hεnu : 0 ≤ ε * saddleNu 1 (Real.log N) := mul_nonneg hε.le hnu
  have hpu : (1 : ℝ) ≤ (N : ℝ) *
      Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hεnu])) hnr.le)
  calc
    _ ≤ 3 * (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) +
        (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := add_le_add hu hpu
    _ = _ := by ring

end PaperP1.ReciprocalOddPivotTripleScale
