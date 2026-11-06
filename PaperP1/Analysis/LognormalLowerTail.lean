module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.GaussianSlopeDecay

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalLowerTail
open Finset PaperP1 LognormalSieveWeight
open scoped Classical

theorem weight_bound (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    weight A x ≤ Real.exp 4*x^3/A^3 := by
  have hG := GaussianSlopeDecay.quadratic_bound (Real.log (x/A)) (-4)
  have hG' : Real.exp (-(Real.log (x/A))^2) ≤ Real.exp 4*Real.exp (4*Real.log (x/A)) := by
    norm_num only [neg_sq,neg_neg,show (4 : ℝ)^2/4=4 by norm_num] at hG
    exact hG
  have hPower : Real.exp (4*Real.log (x/A))=(x/A)^4 := by
    have hh := Real.exp_nat_mul (Real.log (x/A)) 4
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [Real.exp_log (div_pos hx hA)] using hh
  rw [hPower] at hG'
  rw [gaussian_identity A x hA hx]
  calc
    _ ≤ (A/x)*(Real.exp 4*(x/A)^4) := mul_le_mul_of_nonneg_left hG' (div_nonneg hA.le hx.le)
    _ = _ := by field_simp [hA.ne',hx.ne']

theorem integer_head_bound (A t : ℝ) (hA : 0 < A) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (weight A n : ℂ)*LogarithmicExponentialSum.function t n‖ ≤
      Real.exp 4*(N : ℝ)^4/A^3 := by
  have hCard : (Icc 1 N).card=N := by simp
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖(weight A n : ℂ)*LogarithmicExponentialSum.function t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, Real.exp 4*(N : ℝ)^3/A^3 := by
      apply sum_le_sum
      intro n hn
      have hnp : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A n),LogarithmicExponentialSum.function_norm,mul_one]
      exact (weight_bound A n hA hnp).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n)
          (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N) 3) (Real.exp_pos 4).le) (by positivity))
    _ = (N : ℝ)*(Real.exp 4*(N : ℝ)^3/A^3) := by rw [sum_const,nsmul_eq_mul,hCard]
    _ = _ := by ring

theorem sqrt_head_bound (A t : ℝ) (hA : 0 < A) :
    ‖∑ n ∈ Icc 1 (⌈Real.sqrt A⌉₊-1), (weight A n : ℂ)*LogarithmicExponentialSum.function t n‖ ≤ Real.exp 4/A := by
  have hSP : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hN : 1 ≤ ⌈Real.sqrt A⌉₊ := by have hh := Nat.ceil_pos.mpr hSP; omega
  have hCut : ((⌈Real.sqrt A⌉₊-1 : ℕ) : ℝ) ≤ Real.sqrt A := by
    rw [Nat.cast_sub hN,Nat.cast_one]
    have hh := (Nat.ceil_lt_add_one (Real.sqrt_nonneg A)).le
    linarith only [hh]
  have hPower := pow_le_pow_left₀ (Nat.cast_nonneg (⌈Real.sqrt A⌉₊-1)) hCut 4
  have hS4 : (Real.sqrt A)^4=A^2 := by
    rw [show (4 : ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt hA.le]
  rw [hS4] at hPower
  calc
    _ ≤ Real.exp 4*((⌈Real.sqrt A⌉₊-1 : ℕ) : ℝ)^4/A^3 := integer_head_bound A t hA _
    _ ≤ Real.exp 4*A^2/A^3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPower (Real.exp_pos 4).le) (by positivity)
    _ = _ := by field_simp [hA.ne']
end PaperP1.LognormalLowerTail
