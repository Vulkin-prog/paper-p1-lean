module

public import PaperP1.Analysis.SparseGramEnvelope

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedOrderLogarithmicScale
open PaperP1

def exponent (n : ℕ) : ℝ := 1/(16*(n : ℝ))

def scale (n : ℕ) (x y : ℝ) : ℝ := x^(1+1/(2*(n : ℝ)))/y^(1/(n : ℝ))

theorem scale_pos (n : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < scale n x y := by
  unfold scale
  exact div_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)

theorem scale_power (n : ℕ) (hn : 0 < n) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (scale n x y)^n=x^((n : ℝ)+1/2)/y := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hX : (x^(1+1/(2*(n : ℝ))))^n=x^((n : ℝ)+1/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    congr 1
    field_simp
  have hY : (y^(1/(n : ℝ)))^n=y := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hy.le]
    have he : (1/(n : ℝ))*(n : ℝ)=1 := by field_simp
    rw [he,Real.rpow_one]
  unfold scale
  rw [div_pow,hX,hY]

theorem scale_power_times (n : ℕ) (hn : 0 < n) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    y*(scale n x y)^n=x^((n : ℝ)+1/2) := by
  rw [scale_power n hn x y hx hy]
  field_simp

theorem scale_bounds (n : ℕ) (hn : 0 < n) (x y : ℝ) (hx : 1 ≤ x) (hy : 0 < y)
    (hLower : x^(3/4 : ℝ) ≤ y) (hUpper : y ≤ x^((n : ℝ)+1/4)) :
    x^(1/(4*(n : ℝ))) ≤ scale n x y ∧ scale n x y ≤ x^(1-1/(4*(n : ℝ))) := by
  have hxp : 0 < x := by linarith only [hx]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hInv : 0 ≤ 1/(n : ℝ) := by positivity
  have hLowPow := Real.rpow_le_rpow (Real.rpow_nonneg hxp.le (3/4 : ℝ)) hLower hInv
  have hUpPow := Real.rpow_le_rpow hy.le hUpper hInv
  rw [← Real.rpow_mul hxp.le] at hLowPow hUpPow
  have hNum : 0 ≤ x^(1+1/(2*(n : ℝ))) := Real.rpow_nonneg hxp.le _
  have hYP : 0 < y^(1/(n : ℝ)) := Real.rpow_pos_of_pos hy _
  have hBase : 0 < x^((3/4 : ℝ)*(1/(n : ℝ))) := Real.rpow_pos_of_pos hxp _
  constructor
  · have hh := div_le_div_of_nonneg_left hNum hYP hUpPow
    have he : x^(1+1/(2*(n : ℝ)))/x^(((n : ℝ)+1/4)*(1/(n : ℝ)))=x^(1/(4*(n : ℝ))) := by
      rw [← Real.rpow_sub hxp]
      congr 1
      field_simp
      ring
    exact he.symm.le.trans hh
  · have hh := div_le_div_of_nonneg_left hNum hBase hLowPow
    have he : x^(1+1/(2*(n : ℝ)))/x^((3/4 : ℝ)*(1/(n : ℝ)))=x^(1-1/(4*(n : ℝ))) := by
      rw [← Real.rpow_sub hxp]
      congr 1
      field_simp
      ring
    exact hh.trans_eq he

theorem floor_half_bounds (u : ℝ) (hu : 2 ≤ u) :
    u/2 ≤ (⌊u⌋₊ : ℝ) ∧ (⌊u⌋₊ : ℝ) ≤ u ∧ 1 ≤ ⌊u⌋₊ := by
  have hFloor := Nat.lt_floor_add_one u
  exact ⟨by linarith only [hFloor,hu],Nat.floor_le (by linarith only [hu]),Nat.le_floor (by norm_num; linarith only [hu])⟩
end PaperP1.FixedOrderLogarithmicScale
