module

public import PaperP1.Analysis.AmplificationBudgetBound

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeMomentExponentialBudget
open Finset PaperP1
open scoped Classical

theorem budget_bound (x z : ℝ) (hx : 2 ≤ x) (hz : 0 < z) (hlog : Real.log z=x)
    (k : ℕ) (hk : (k : ℝ) ≤ z) (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    AmplifiedPrimeProductMean.budget k P ≤ Real.exp (7*(k : ℝ)*x) := by
  have hbase : 0 < 32*z^2 := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk := pow_le_pow_left₀ hk0 hk 2
  have hArg : 32*(k : ℝ)^2 ≤ 32*z^2 := mul_le_mul_of_nonneg_left hkk (by norm_num)
  have hlogTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog32 : Real.log (32 : ℝ) ≤ 5 := by
    have he : (32 : ℝ)=2^5 := by norm_num
    rw [he,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlogTwo]
  have hLogBase : Real.log (32*z^2) ≤ 7*x := by
    rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 2 hz.ne'),Real.log_pow,hlog]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlog32,hx]
  calc
    _ ≤ (32*(k : ℝ)^2)^k := AmplificationBudgetBound.budget_power_bound k P hMass
    _ ≤ (32*z^2)^k := pow_le_pow_left₀ (by positivity) hArg k
    _ = Real.exp ((k : ℝ)*Real.log (32*z^2)) := by rw [Real.exp_nat_mul,Real.exp_log hbase]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hLogBase hk0])

theorem polynomial_factor_bound (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : 0 ≤ r) (hrk : r ≤ k) :
    Real.exp (6*r)*(2+9*r^2) ≤ Real.exp (12*(k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hSq := pow_le_pow_left₀ hr hrk 2
  have hPoly : 2+9*r^2 ≤ (1+3*(k : ℝ))^2 := by nlinarith only [hSq,hkR]
  have hExp := Real.add_one_le_exp (3*(k : ℝ))
  have hE2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1+3*(k : ℝ)) (by simpa only [add_comm] using hExp) 2
  have he : (Real.exp (3*(k : ℝ)))^2=Real.exp (6*(k : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hE2
  have hFirst := Real.exp_le_exp.mpr (by linarith only [hrk] : 6*r ≤ 6*(k : ℝ))
  calc
    _ ≤ Real.exp (6*(k : ℝ))*Real.exp (6*(k : ℝ)) :=
      mul_le_mul hFirst (hPoly.trans hE2) (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem combined_bound (x z C : ℝ) (hx : 2 ≤ x) (hz : x^5 ≤ z)
    (hlog : Real.log z=x) (hCe : C ≤ Real.exp x)
    (k H : ℕ) (hk : 1 ≤ k) (hH : 1 ≤ H) (hkz : (k : ℝ) ≤ z)
    (hkr : (k : ℝ) ≤ 3*z/x^2) (P : Finset ℕ) (hMass : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    C*Real.exp (6*((k : ℝ)/(H : ℝ)))*(2+9*((k : ℝ)/(H : ℝ))^2)*
      AmplifiedPrimeProductMean.budget k P ≤ Real.exp (40*z/x) := by
  have hxp : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hz2 : x^2 ≤ z := (pow_le_pow_right₀ hx1 (by norm_num : (2 : ℕ) ≤ 5)).trans hz
  have hzp : 0 < z := (pow_pos hxp 2).trans_le hz2
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by linarith only [hHR]
  have hrk : (k : ℝ)/(H : ℝ) ≤ k := (div_le_iff₀ hHp).mpr (by
    have hh := mul_le_mul_of_nonneg_left hHR (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    simpa only [mul_one] using hh)
  have hPoly := polynomial_factor_bound k hk ((k : ℝ)/(H : ℝ)) (by positivity) hrk
  have hBudget := budget_bound x z hx hzp hlog k hkz P hMass
  have hprod : C*Real.exp (6*((k : ℝ)/(H : ℝ)))*(2+9*((k : ℝ)/(H : ℝ))^2)*
      AmplifiedPrimeProductMean.budget k P ≤ Real.exp (x+12*(k : ℝ)+7*(k : ℝ)*x) := by
    calc
      _ = C*(Real.exp (6*((k : ℝ)/(H : ℝ)))*(2+9*((k : ℝ)/(H : ℝ))^2))*AmplifiedPrimeProductMean.budget k P := by ring
      _ ≤ (Real.exp x*Real.exp (12*(k : ℝ)))*Real.exp (7*(k : ℝ)*x) :=
        mul_le_mul (mul_le_mul hCe hPoly (by positivity) (Real.exp_pos _).le) hBudget
          (AmplifiedPrimeProductMean.budget_nonneg k P) (by positivity)
      _ = _ := by rw [← Real.exp_add,← Real.exp_add]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hxRatio : x ≤ z/x := (le_div_iff₀ hxp).mpr (by simpa only [pow_two] using hz2)
  have hWeight : 13*(k : ℝ)*x ≤ 39*z/x := by
    have hh := mul_le_mul_of_nonneg_right hkr (show 0 ≤ 13*x by positivity)
    have he : (3*z/x^2)*(13*x)=39*z/x := by field_simp; ring
    rw [he] at hh
    nlinarith only [hh]
  apply hprod.trans
  apply Real.exp_le_exp.mpr
  have hSmall := mul_le_mul_of_nonneg_left hx hk0
  simp only [div_eq_mul_inv] at hxRatio hWeight ⊢
  nlinarith only [hSmall,hxRatio,hWeight]

theorem final_exponent_bound (x z : ℝ) (hx : 100000 ≤ x) (hz : x^5 ≤ z) :
    40*z/x+(z+x^3)/20 ≤ z/19 := by
  have hxp : 0 < x := by linarith only [hx]
  have hzp : 0 < z := (pow_pos hxp 5).trans_le hz
  have hFirst : 40*z/x ≤ z/1000 := (div_le_iff₀ hxp).mpr (by
    have hh := mul_le_mul_of_nonneg_left hx hzp.le
    nlinarith only [hh,hzp])
  have hxSq : 50 ≤ x^2 := by
    have hh := mul_le_mul_of_nonneg_left hx hxp.le
    nlinarith only [hh,hx]
  have hSecond : x^3/20 ≤ z/1000 := by
    have hh := mul_le_mul_of_nonneg_right hxSq (pow_nonneg hxp.le 3)
    nlinarith only [hh,hz]
  linarith only [hFirst,hSecond,hzp]
end PaperP1.PrimeMomentExponentialBudget
