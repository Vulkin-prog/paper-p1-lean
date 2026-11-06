module

public import PaperP1.Analysis.RecursiveLogarithmicDifferencing

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RecursiveBudgetPower
open PaperP1

theorem constant_square (C : ℝ) (hC : 4 ≤ C) : 4+2*C ≤ C^2 := by
  nlinarith only [hC,sq_nonneg (C-2)]

theorem bound (K n : ℕ) (x β C ε : ℝ) (hx : 1 ≤ x) (hβ : 0 ≤ β) (hC : 4 ≤ C)
    (hK : x^β/2 ≤ (K : ℝ)) (hε0 : 0 ≤ ε) (hε : ε ≤ C*x^(-β)) :
    RecursiveLogarithmicDifferencing.budget K n ε ≤ C*x^(-β/(2 : ℝ)^n) := by
  have hxp : 0 < x := by linarith only [hx]
  have hCp : 0 < C := by linarith only [hC]
  have hKLow : 0 < x^β/2 := div_pos (Real.rpow_pos_of_pos hxp _) (by norm_num)
  have hKp : (0 : ℝ) < K := hKLow.trans_le hK
  have hInv : 2/(K : ℝ) ≤ 4*x^(-β) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hKLow hK
    calc
      _ ≤ 2/(x^β/2) := hh
      _ = _ := by rw [div_div_eq_mul_div,Real.rpow_neg hxp.le]; ring
  induction n with
  | zero => simpa only [RecursiveLogarithmicDifferencing.budget,pow_zero,div_one] using hε
  | succ n ih =>
    have hTwo : (1 : ℝ) ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
    have hTwoPos : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have hRatio : β/(2 : ℝ)^n ≤ β := (div_le_iff₀ hTwoPos).mpr (by
      have hh := mul_le_mul_of_nonneg_left hTwo hβ
      simpa only [mul_one] using hh)
    have hPow := Real.rpow_le_rpow_of_exponent_le hx (show -β ≤ -β/(2 : ℝ)^n by
      have he : -β/(2 : ℝ)^n=-(β/(2 : ℝ)^n) := by ring
      rw [he]
      linarith only [hRatio])
    have hFirst := hInv.trans (mul_le_mul_of_nonneg_left hPow (by norm_num : (0 : ℝ) ≤ 4))
    have hSecond := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
    have hArgBound : 2/(K : ℝ)+2*RecursiveLogarithmicDifferencing.budget K n ε ≤
        C^2*x^(-β/(2 : ℝ)^n) := by
      have hh : 2/(K : ℝ)+2*RecursiveLogarithmicDifferencing.budget K n ε ≤
          (4+2*C)*x^(-β/(2 : ℝ)^n) := by nlinarith only [hFirst,hSecond]
      exact hh.trans (mul_le_mul_of_nonneg_right (constant_square C hC) (Real.rpow_nonneg hxp.le _))
    have hRpow : (x^(-β/(2 : ℝ)^(n+1)))^2=x^(-β/(2 : ℝ)^n) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hxp.le]
      congr 1
      rw [pow_succ]
      field_simp
      norm_num only [Nat.cast_ofNat]
    have hSquare : (C*x^(-β/(2 : ℝ)^(n+1)))^2=C^2*x^(-β/(2 : ℝ)^n) := by rw [mul_pow,hRpow]
    have hBudget := RecursiveLogarithmicDifferencing.budget_nonneg K n ε hε0
    have hArgNN : 0 ≤ 2/(K : ℝ)+2*RecursiveLogarithmicDifferencing.budget K n ε := by positivity
    have hTarget : 0 ≤ C*x^(-β/(2 : ℝ)^(n+1)) := mul_nonneg hCp.le (Real.rpow_nonneg hxp.le _)
    change Real.sqrt (2/(K : ℝ)+2*RecursiveLogarithmicDifferencing.budget K n ε) ≤ C*x^(-β/(2 : ℝ)^(n+1))
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hTarget).mp
    rw [Real.sq_sqrt hArgNN,hSquare]
    exact hArgBound
end PaperP1.RecursiveBudgetPower
