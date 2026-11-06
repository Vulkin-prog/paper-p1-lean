module

public import PaperP1.Analysis.PolynomialLogarithmicCancellation
public import PaperP1.Analysis.DampedLogarithmicIntegral
public import PaperP1.Analysis.DyadicLongCutoff
public import PaperP1.Analysis.ZetaCutoffGeometry

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ZetaMiddleEstimate
open Finset Filter PaperP1 PolynomialLogarithmicCancellation ZetaCutoffGeometry
open scoped Classical

theorem uniform_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 0 ≤ σ →
      ‖∑ n ∈ Ico (lower α |t|) (upper |t|), DampedLogarithmicIntegral.integrand σ t n‖ ≤
        ((Real.log 2+2*Real.log |t|)/Real.log 2+1)*constant (1/α)/
          |t|^(α*decay (1/4) (1/α)) := by
  obtain ⟨N₀,hN₀,hLong⟩ := DyadicLongCutoff.uniform_bound (1/4) (1/α) (by norm_num) (by positivity)
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp (lower_eventually α hα0 N₀)
  refine ⟨max 8 T₁,le_max_left _ _,?_⟩
  intro t ht σ hσ
  have ht8 : 8 ≤ |t| := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ |t| := by linarith only [ht8]
  have htP : 0 < |t| := by linarith only [ht8]
  have hLower := lower_bounds α |t| hα0.le ht1
  have hUpper := upper_bounds |t| ht1
  have hN : N₀ ≤ lower α |t| := hT₁ |t| ((le_max_right _ _).trans ht)
  have hBound := hLong (lower α |t|) hN (upper |t|) (ordered α |t| hα1 ht1) t
    (lower_frequency α |t| hα0.le hα1 ht8) (upper_frequency α |t| hα0 ht1) σ hσ
  have hLog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hLogY : 0 ≤ Real.log |t| := Real.log_nonneg ht1
  have hLog := div_le_div_of_nonneg_right (logarithmic_upper |t| ht1) hLog2.le
  have hC : 0 ≤ constant (1/α) := by linarith only [constant_four_le (1/α)]
  have hFactor : 0 ≤ (Real.log 2+2*Real.log |t|)/Real.log 2+1 := by positivity
  have hPower : |t|^(α*decay (1/4) (1/α)) ≤
      (lower α |t| : ℝ)^(decay (1/4) (1/α)) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg htP.le α) hLower.2.1
      (decay_pos (1/4) (1/α) (by norm_num)).le
    simpa only [← Real.rpow_mul htP.le] using hh
  calc
    _ ≤ (Real.log (upper |t| : ℝ)/Real.log 2+1)*constant (1/α)/
        (lower α |t| : ℝ)^(decay (1/4) (1/α)) := hBound
    _ ≤ ((Real.log 2+2*Real.log |t|)/Real.log 2+1)*constant (1/α)/
        (lower α |t| : ℝ)^(decay (1/4) (1/α)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (add_le_add hLog (le_refl 1)) hC)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hFactor hC)
      (Real.rpow_pos_of_pos htP _) hPower
end PaperP1.ZetaMiddleEstimate
