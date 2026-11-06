module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Exact leading-coefficient limits for actual quadratic and cubic values at natural arguments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialNatRatioLimits

open Filter Topology

theorem quadratic (A B C : ℝ) :
    Tendsto (fun n : ℕ ↦ (A * (n : ℝ) ^ 2 + B * (n : ℝ) + C) / (n : ℝ) ^ 2)
      atTop (𝓝 A) := by
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦ A + B * (n : ℝ)⁻¹ + C * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 A) := by
    convert (tendsto_const_nhds.add (hi.const_mul B)).add ((hi.pow 2).const_mul C) using 1; norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]

theorem cubic (A B C D : ℝ) :
    Tendsto (fun n : ℕ ↦ (A * (n : ℝ) ^ 3 + B * (n : ℝ) ^ 2 + C * (n : ℝ) + D) / (n : ℝ) ^ 3)
      atTop (𝓝 A) := by
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦ A + B * (n : ℝ)⁻¹ + C * ((n : ℝ)⁻¹) ^ 2 +
      D * ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 A) := by
    convert ((tendsto_const_nhds.add (hi.const_mul B)).add ((hi.pow 2).const_mul C)).add
      ((hi.pow 3).const_mul D) using 1; norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]

end PaperP1.PolynomialNatRatioLimits
