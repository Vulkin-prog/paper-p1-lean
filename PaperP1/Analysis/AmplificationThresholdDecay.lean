module

public import PaperP1.Analysis.AmplifiedPrimeProductMean
public import PaperP1.Analysis.AmplificationBudgetBound

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.AmplificationThresholdDecay
open Finset PaperP1
open scoped Classical

theorem logarithmic_power_bound (x u q : ℝ) (hx : 2 ≤ x) (hq : 0 < q) (k : ℕ)
    (hu : 999*Real.log x ≤ Real.log u) (hk : (k : ℝ)*Real.log u ≤ Real.log q) :
    x^(31*k) ≤ q^(1/25 : ℝ) := by
  have hxp : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hn := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hlogx
  have hlog : (((31*k : ℕ) : ℝ))*Real.log x ≤ Real.log q*(1/25 : ℝ) := by
    push_cast
    nlinarith only [hmul,hk,hn]
  have he : x^(31*k)=Real.exp (((31*k : ℕ) : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hxp]
  rw [he,Real.rpow_def_of_pos hq]
  exact Real.exp_le_exp.mpr hlog

theorem mixed_weight_bound (x u q : ℝ) (hx : 2 ≤ x) (hq : 0 < q) (k : ℕ) (hkcap : (k : ℝ) ≤ x^3)
    (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1)
    (hu : 999*Real.log x ≤ Real.log u) (hk : (k : ℝ)*Real.log u ≤ Real.log q) :
    ((q^(-1/40 : ℝ))^2/(1/x^10)^(2*k))*AmplifiedPrimeProductMean.budget k P ≤ q^(-1/100 : ℝ) := by
  have hb := (AmplificationBudgetBound.threshold_budget_bound x hx k hkcap P hMass).trans
    (logarithmic_power_bound x u q hx hq k hu hk)
  calc
    _ = (q^(-1/40 : ℝ))^2*(AmplifiedPrimeProductMean.budget k P/(1/x^10)^(2*k)) := by ring
    _ ≤ (q^(-1/40 : ℝ))^2*q^(1/25 : ℝ) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← Real.rpow_two,← Real.rpow_mul hq.le,← Real.rpow_add hq]
      norm_num
end PaperP1.AmplificationThresholdDecay
