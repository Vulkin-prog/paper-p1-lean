module

public import PaperP1.Analysis.ReciprocalOddPivotUpper

/-! # Exact full-population reciprocal odd-pivot logarithmic scale

The ordinary largest-prime-factor asymptotic is the sole explicit
literature input. All square-part transport and scale estimates are
proved internally before this conclusion is assembled.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalOddPivotFullScale

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.HardSaddleExplicitScale
  PaperP1.OrdinaryReciprocalPrimeInput PaperP1.ReciprocalOddPivots

theorem uniform_full_sandwich (hinput : EIPInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ max X₀ 2,
      (X : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log X) - ε * saddleNu 1 (Real.log X)) ≤ pivotSum X ∧
      pivotSum X ≤ (X : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log X) + ε * saddleNu 1 (Real.log X)) := by
  obtain ⟨XI, hI⟩ := hinput (ε / 3) (by positivity)
  obtain ⟨XU, hU⟩ := PaperP1.ReciprocalOddPivotUpper.uniform_finite_upper hinput (ε / 3) (by positivity)
  have hnatlog : Tendsto (fun X : ℕ ↦ Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgap := (tendsto_hard_saddle_gap.abs).comp hnatlog
  have hgap' : Tendsto (fun X : ℕ ↦
      |(2 * saddleCutoff 1 (Real.log X) - explicitScale (Real.log X)) / saddleNu 1 (Real.log X)|)
      atTop (nhds 0) := by simpa only [Function.comp_def, abs_zero] using hgap
  have hfactor := ((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_atTop
    (by positivity : 0 < ε / 3)).comp hnatlog
  obtain ⟨XG, hG⟩ := eventually_atTop.mp
    ((hgap'.eventually (eventually_lt_nhds (by positivity : 0 < ε / 3))).and
      ((hfactor.eventually (eventually_ge_atTop (Real.log 6))).and
        (hnatlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) 1)))))
  refine ⟨max XI (max XU XG), ?_⟩
  intro X hX
  obtain ⟨hgapX, hfactorX, hdomain⟩ := hG X (by omega)
  have hH : 0 < Real.log X := by have := (le_max_right _ _).trans hdomain; linarith
  have hV : 0 < saddleCutoff 1 (Real.log X) := saddleCutoff_pos (by norm_num) (by order)
  have hnu : 0 < saddleNu 1 (Real.log X) := div_pos hH hV
  rw [abs_div, abs_of_pos hnu] at hgapX
  have hgapmul := (div_le_iff₀ hnu).mp hgapX.le
  obtain ⟨hgaplo, hgaphi⟩ := abs_le.mp hgapmul
  have hεnu : 0 ≤ ε * saddleNu 1 (Real.log X) := mul_nonneg hε.le hnu.le
  have hfac : 6 ≤ Real.exp ((ε / 3) * saddleNu 1 (Real.log X)) := by
    simpa only [Function.comp_def, Real.exp_log (by norm_num : (0 : ℝ) < 6)] using Real.exp_le_exp.mpr hfactorX
  have hx : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  constructor
  · calc
      _ ≤ (X : ℝ) * Real.exp (-explicitScale (Real.log X) - (ε / 3) * saddleNu 1 (Real.log X)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hgaplo, hεnu])) hx
      _ ≤ primeSum X := (hI X (by omega)).1
      _ ≤ pivotSum X := primeSum_le_pivotSum X
  · calc
      _ ≤ 6 * X * Real.exp (-explicitScale (Real.log X) + (ε / 3) * saddleNu 1 (Real.log X)) := hU X (by omega)
      _ ≤ Real.exp ((ε / 3) * saddleNu 1 (Real.log X)) * X *
          Real.exp (-explicitScale (Real.log X) + (ε / 3) * saddleNu 1 (Real.log X)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hx) (Real.exp_pos _).le
      _ = (X : ℝ) * Real.exp (-explicitScale (Real.log X) + (2 * ε / 3) * saddleNu 1 (Real.log X)) := by
        calc
          _ = (X : ℝ) * (Real.exp ((ε / 3) * saddleNu 1 (Real.log X)) *
              Real.exp (-explicitScale (Real.log X) + (ε / 3) * saddleNu 1 (Real.log X))) := by ring
          _ = (X : ℝ) * Real.exp ((ε / 3) * saddleNu 1 (Real.log X) +
              (-explicitScale (Real.log X) + (ε / 3) * saddleNu 1 (Real.log X))) := by rw [← Real.exp_add]
          _ = _ := by congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hgaphi])) hx

end PaperP1.ReciprocalOddPivotFullScale
