module

public import PaperP1.Analysis.PowerSeriesTail
public import PaperP1.Analysis.DampedDirichletTail
public import PaperP1.Analysis.ActualZetaTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PositiveZetaBound
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem total_bound (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    PowerSeriesTail.total (1+σ) ≤ 1+2/σ := by
  have hS : 1 < 1+σ := by linarith only [hσ0]
  have hSplit := (PowerSeriesTail.summable_weight (1+σ) hS).tsum_eq_zero_add
  have hTailEq : (∑' n : ℕ, PowerSeriesTail.weight (1+σ) (n+1))=PowerSeriesTail.tail (1+σ) 1 := by
    have hh := PowerSeriesTail.tail_eq_shifted (1+σ) 1 hS (by norm_num)
    simpa only [PowerSeriesTail.weight,Nat.floor_one,Nat.cast_add,Nat.cast_one,add_assoc] using hh.symm
  change PowerSeriesTail.total (1+σ)=PowerSeriesTail.weight (1+σ) 0+
    ∑' n : ℕ, PowerSeriesTail.weight (1+σ) (n+1) at hSplit
  rw [hTailEq] at hSplit
  have hOne : PowerSeriesTail.weight (1+σ) 0=1 := by simp [PowerSeriesTail.weight]
  rw [hSplit,hOne]
  have hTail := PowerSeriesTail.tail_le_power (1+σ) hS 1 (by norm_num)
  have hTail' : PowerSeriesTail.tail (1+σ) 1 ≤ (2 : ℝ)^σ/σ := by
    simpa only [PowerSeriesTail.constant,add_sub_cancel_left,Real.one_rpow,mul_one] using hTail
  have hPower : (2 : ℝ)^σ ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hσ1
  exact add_le_add (le_refl 1) (hTail'.trans (div_le_div_of_nonneg_right hPower hσ0.le))

theorem norm_bound (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ‖riemannZeta (ActualZetaTail.argument σ 0)‖ ≤ 1+2/σ := by
  have hSum := DampedDirichletTail.summable_terms σ 0 hσ0
  have hNorm := hSum.norm
  have hZero : ‖DampedLogarithmicIntegral.integrand σ 0 0‖=0 := by
    simp [DampedLogarithmicIntegral.integrand]
  have hWeightEq : (∑' n : ℕ, ‖DampedLogarithmicIntegral.integrand σ 0 n‖)=
      PowerSeriesTail.total (1+σ) := by
    rw [hNorm.tsum_eq_zero_add,Nat.cast_zero,hZero,zero_add]
    unfold PowerSeriesTail.total
    apply tsum_congr
    intro n
    rw [DampedDirichletTail.term_norm σ 0 hσ0.le (n+1)]
    unfold PowerSeriesTail.weight
    have hp : (0 : ℝ) < n+1 := by positivity
    simp only [Nat.cast_add,Nat.cast_one]
    rw [Real.rpow_neg hp.le,one_div]
  rw [← ActualZetaTail.series_eq_zeta σ 0 hσ0]
  unfold DampedDirichletTail.series
  exact ((norm_tsum_le_tsum_norm hNorm).trans_eq hWeightEq).trans (total_bound σ hσ0 hσ1)

theorem logarithmic_norm_bound (X : ℕ) (hLog : 1 ≤ Real.log (X : ℝ)) :
    ‖riemannZeta (ActualZetaTail.argument (1/Real.log (X : ℝ)) 0)‖ ≤ 3*Real.log (X : ℝ) := by
  have hLP : 0 < Real.log (X : ℝ) := by linarith only [hLog]
  have hSigma : 1/Real.log (X : ℝ) ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hLog
    simpa only [div_one] using hh
  have hBound := norm_bound (1/Real.log (X : ℝ)) (by positivity) hSigma
  have he : 2/(1/Real.log (X : ℝ))=2*Real.log (X : ℝ) := by rw [div_div_eq_mul_div,div_one]
  rw [he] at hBound
  linarith only [hBound,hLog]
end PaperP1.PositiveZetaBound
