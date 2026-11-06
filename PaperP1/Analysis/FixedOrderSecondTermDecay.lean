module

public import PaperP1.Analysis.TerminalLogarithmicBudget
public import PaperP1.Analysis.FixedOrderLogarithmicScale

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedOrderSecondTermDecay
open PaperP1 FixedOrderLogarithmicScale

theorem exponent_power (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
    (x^(exponent n))^n=x^(1/16 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  congr 1
  unfold exponent
  field_simp

theorem quotient_identity (n : ℕ) (x : ℝ) (hx : 0 < x) :
    x^((n : ℝ)+1/2)*x^(1/16 : ℝ)/x^(n+1)=1/x^(7/16 : ℝ) := by
  rw [← Real.rpow_add hx,← Real.rpow_natCast,← Real.rpow_sub hx]
  have he : ((n : ℝ)+1/2+1/16)-((n+1 : ℕ) : ℝ)=-(7/16 : ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg hx.le,one_div]

theorem second_bound (n X A K : ℕ) (hn : 0 < n) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < |t|)
    (hA : (A : ℝ) ≤ scale n X |t|) (hK : (K : ℝ) ≤ (X : ℝ)^(exponent n)) :
    |t| * (n.factorial : ℝ)*((A*K : ℕ) : ℝ)^n/(X : ℝ)^(n+1) ≤
      (n.factorial : ℝ)/(X : ℝ)^(7/16 : ℝ) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith only [hXR]
  have hG := scale_pos n X |t| hXp ht
  have hProd : ((A*K : ℕ) : ℝ) ≤ scale n X |t| *(X : ℝ)^(exponent n) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hA hK (Nat.cast_nonneg K) hG.le
  have hPow := pow_le_pow_left₀ (Nat.cast_nonneg (A*K) : (0 : ℝ) ≤ (A*K : ℕ)) hProd n
  rw [mul_pow,exponent_power n hn X hXp] at hPow
  have hNum := mul_le_mul_of_nonneg_left hPow (show 0 ≤ |t| * (n.factorial : ℝ) by positivity)
  have hDiv := div_le_div_of_nonneg_right hNum (pow_nonneg hXp.le (n+1))
  calc
    _ ≤ (|t| * (n.factorial : ℝ)*((scale n X |t|)^n*(X : ℝ)^(1/16 : ℝ)))/(X : ℝ)^(n+1) := hDiv
    _ = (n.factorial : ℝ)*(|t| * (scale n X |t|)^n*(X : ℝ)^(1/16 : ℝ)/(X : ℝ)^(n+1)) := by ring
    _ = (n.factorial : ℝ)*((X : ℝ)^((n : ℝ)+1/2)*(X : ℝ)^(1/16 : ℝ)/(X : ℝ)^(n+1)) := by
      rw [scale_power_times n hn X |t| hXp ht]
    _ = (n.factorial : ℝ)*(1/(X : ℝ)^(7/16 : ℝ)) := by rw [quotient_identity n X hXp]
    _ = _ := by ring
end PaperP1.FixedOrderSecondTermDecay
