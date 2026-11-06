module

public import PaperP1.Analysis.PrimeMomentExponentialBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalPrimeCardBudget
open Finset PaperP1
open scoped Classical

theorem threshold_identity (z : ℝ) (hz : 0 < z) (x : ℝ) (hLog : Real.log z=x) (k : ℕ) :
    ((1/z^100)^(2*k))⁻¹=Real.exp (200*(k : ℝ)*x) := by
  calc
    _ = z^(200*k) := by
      simp only [one_div,inv_pow,inv_inv]
      rw [← pow_mul]
      congr 1
      omega
    _ = Real.exp (((200*k : ℕ) : ℝ)*Real.log z) := by
      rw [Real.exp_nat_mul,Real.exp_log hz]
    _ = _ := by rw [hLog]; congr 1; push_cast; ring

theorem weighted_bound (x z C : ℝ) (hx : 2 ≤ x) (hz : x^5 ≤ z)
    (hLog : Real.log z=x) (hC : C ≤ Real.exp (x^2)) (k : ℕ) (hk : (k : ℝ) ≤ 3*x)
    (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    C*AmplifiedPrimeProductMean.budget k P/(1/z^100)^(2*k) ≤ Real.exp (1000*x^2) := by
  have hxp : 0 < x := by linarith only [hx]
  have hzp : 0 < z := (pow_pos hxp 5).trans_le hz
  have hx4 : 3 ≤ x^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 4
    norm_num at hh
    linarith only [hh]
  have hkz : (k : ℝ) ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hx4 hxp.le
    have hLow : 3*x ≤ x^5 := by nlinarith only [hh]
    exact hk.trans (hLow.trans hz)
  have hBudget := PrimeMomentExponentialBudget.budget_bound x z hx hzp hLog k hkz P hMass
  have hProd := mul_le_mul hC hBudget (AmplifiedPrimeProductMean.budget_nonneg k P) (Real.exp_pos _).le
  rw [div_eq_mul_inv,threshold_identity z hzp x hLog k]
  calc
    _ ≤ (Real.exp (x^2)*Real.exp (7*(k : ℝ)*x))*Real.exp (200*(k : ℝ)*x) :=
      mul_le_mul_of_nonneg_right hProd (Real.exp_pos _).le
    _ = Real.exp (x^2+7*(k : ℝ)*x+200*(k : ℝ)*x) := by rw [← Real.exp_add,← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hk hxp.le
      nlinarith only [hh,sq_nonneg x]
end PaperP1.FinalPrimeCardBudget
