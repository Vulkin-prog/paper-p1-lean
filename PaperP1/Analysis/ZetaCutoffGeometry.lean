module

public import PaperP1.Analysis.PolynomialLogarithmicCancellation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ZetaCutoffGeometry
open Finset Filter PaperP1
open scoped Classical

def lower (α y : ℝ) : ℕ := ⌈y^α⌉₊

def upper (y : ℝ) : ℕ := ⌈y^2⌉₊

theorem ceiling_bounds (u : ℝ) (hu : 1 ≤ u) :
    1 ≤ ⌈u⌉₊ ∧ u ≤ (⌈u⌉₊ : ℝ) ∧ (⌈u⌉₊ : ℝ) ≤ 2*u := by
  have hLower := Nat.le_ceil u
  have hUpper := (Nat.ceil_lt_add_one (by linarith only [hu] : 0 ≤ u)).le
  have hOne : 1 ≤ ⌈u⌉₊ := by exact_mod_cast (hu.trans hLower)
  exact ⟨hOne,hLower,by linarith only [hu,hUpper]⟩

theorem lower_bounds (α y : ℝ) (hα : 0 ≤ α) (hy : 1 ≤ y) :
    1 ≤ lower α y ∧ y^α ≤ (lower α y : ℝ) ∧ (lower α y : ℝ) ≤ 2*y^α :=
  ceiling_bounds (y^α) (Real.one_le_rpow hy hα)

theorem upper_bounds (y : ℝ) (hy : 1 ≤ y) :
    1 ≤ upper y ∧ y^2 ≤ (upper y : ℝ) ∧ (upper y : ℝ) ≤ 2*y^2 :=
  ceiling_bounds (y^2) (by nlinarith only [hy])

theorem ordered (α y : ℝ) (hα : α ≤ 1) (hy : 1 ≤ y) : lower α y ≤ upper y := by
  apply Nat.ceil_mono
  have hh := Real.rpow_le_rpow_of_exponent_le hy (show α ≤ (2 : ℝ) by linarith only [hα])
  simpa only [Real.rpow_two] using hh

theorem product_bound (α y : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hy : 8 ≤ y) :
    (((2*upper y*lower α y : ℕ) : ℝ)) ≤ y^4 := by
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hLower := (lower_bounds α y hα0 hy1).2.2
  have hUpper := (upper_bounds y hy1).2.2
  have hPow : y^α ≤ y := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy1 hα1
  have hLN : (lower α y : ℝ) ≤ 2*y := by linarith only [hLower,hPow]
  have hProduct := mul_le_mul hUpper hLN (Nat.cast_nonneg _) (by positivity : 0 ≤ 2*y^2)
  push_cast
  nlinarith only [hProduct,mul_nonneg (by nlinarith only [hy] : 0 ≤ y-8) (by positivity : 0 ≤ y^3)]

theorem lower_frequency (α y : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hy : 8 ≤ y) :
    (((2*upper y*lower α y : ℕ) : ℝ))^(1/4 : ℝ) ≤ y := by
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg (2*upper y*lower α y))
    (product_bound α y hα0 hα1 hy) (by norm_num : (0 : ℝ) ≤ 1/4)
  have he : (y^4)^(1/4 : ℝ)=y := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith only [hy] : 0 ≤ y)]
    norm_num
  exact hh.trans_eq he

theorem upper_frequency (α y : ℝ) (hα : 0 < α) (hy : 1 ≤ y) :
    y ≤ (lower α y : ℝ)^(1/α) := by
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ y^α) (lower_bounds α y hα.le hy).2.1
    (by positivity : 0 ≤ 1/α)
  have he : (y^α)^(1/α)=y := by
    rw [← Real.rpow_mul (by linarith only [hy] : 0 ≤ y)]
    rw [mul_one_div_cancel hα.ne',Real.rpow_one]
  exact he.symm.trans_le hh

theorem logarithmic_lower (α y : ℝ) (hα : 0 ≤ α) (hy : 1 ≤ y) :
    Real.log (lower α y : ℝ) ≤ Real.log 2+α*Real.log y := by
  have hp : 0 < y := by linarith only [hy]
  have hN : (0 : ℝ) < lower α y := by exact_mod_cast (lower_bounds α y hα hy).1
  have hh := Real.log_le_log hN (lower_bounds α y hα hy).2.2
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hp α).ne',Real.log_rpow hp] at hh
  exact hh

theorem logarithmic_upper (y : ℝ) (hy : 1 ≤ y) :
    Real.log (upper y : ℝ) ≤ Real.log 2+2*Real.log y := by
  have hp : 0 < y := by linarith only [hy]
  have hM : (0 : ℝ) < upper y := by exact_mod_cast (upper_bounds y hy).1
  have hh := Real.log_le_log hM (upper_bounds y hy).2.2
  rw [Real.log_mul (by norm_num) (pow_pos hp 2).ne',Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

theorem lower_eventually (α : ℝ) (hα : 0 < α) (N₀ : ℕ) :
    ∀ᶠ y : ℝ in atTop, N₀ ≤ lower α y := by
  filter_upwards [(tendsto_rpow_atTop hα).eventually (eventually_ge_atTop (N₀ : ℝ))] with y hy
  exact_mod_cast hy.trans (Nat.le_ceil (y^α))
end PaperP1.ZetaCutoffGeometry
