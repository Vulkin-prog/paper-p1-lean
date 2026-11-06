module

public import PaperP1.Analysis.TerminalLogarithmicBudget
public import PaperP1.Analysis.FixedOrderLogarithmicScale

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedOrderFirstTermDecay
open PaperP1 FixedOrderLogarithmicScale

theorem quotient_identity (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (2*(3 : ℝ)^(n+1)*x^n)/(x^((n : ℝ)+1/2)/(2 : ℝ)^n)=(6 : ℝ)^(n+1)/x^(1/2 : ℝ) := by
  have hc : 2*(3 : ℝ)^(n+1)*(2 : ℝ)^n=(6 : ℝ)^(n+1) := by
    rw [show (6 : ℝ)=2*3 by norm_num,mul_pow]
    simp only [pow_succ]
    ring
  rw [div_div_eq_mul_div]
  calc
    _ = ((2*(3 : ℝ)^(n+1)*(2 : ℝ)^n)*x^n)/x^((n : ℝ)+1/2) := by ring
    _ = ((6 : ℝ)^(n+1)*x^n)/(x^n*x^(1/2 : ℝ)) := by rw [hc,Real.rpow_add hx,Real.rpow_natCast]
    _ = _ := by field_simp [(pow_pos hx n).ne',(Real.rpow_pos_of_pos hx (1/2 : ℝ)).ne']

theorem first_bound (n X A : ℕ) (hn : 0 < n) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < |t|)
    (hHalf : scale n X |t|/2 ≤ (A : ℝ)) :
    2*(3 : ℝ)^(n+1)*(X : ℝ)^n/(|t| * (n.factorial : ℝ)*(A : ℝ)^n) ≤
      (6 : ℝ)^(n+1)/(X : ℝ)^(1/2 : ℝ) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith only [hXR]
  have hG := scale_pos n X |t| hXp ht
  have hApos : (0 : ℝ) < A := (div_pos hG (by norm_num : (0 : ℝ) < 2)).trans_le hHalf
  have hPow := pow_le_pow_left₀ (div_nonneg hG.le (by norm_num : (0 : ℝ) ≤ 2)) hHalf n
  rw [div_pow] at hPow
  have hY := mul_le_mul_of_nonneg_left hPow ht.le
  rw [← mul_div_assoc,scale_power_times n hn X |t| hXp ht] at hY
  have hFactorial : (1 : ℝ) ≤ n.factorial := by
    have hNat : 1 ≤ n.factorial := by have hh := Nat.factorial_pos n; omega
    exact_mod_cast hNat
  have hF := mul_le_mul_of_nonneg_right hFactorial (show 0 ≤ |t| * (A : ℝ)^n by positivity)
  have hDen : (X : ℝ)^((n : ℝ)+1/2)/(2 : ℝ)^n ≤ |t| * (n.factorial : ℝ)*(A : ℝ)^n :=
    hY.trans (by nlinarith only [hF])
  calc
    _ ≤ (2*(3 : ℝ)^(n+1)*(X : ℝ)^n)/((X : ℝ)^((n : ℝ)+1/2)/(2 : ℝ)^n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hDen
    _ = _ := quotient_identity n X hXp
end PaperP1.FixedOrderFirstTermDecay
