module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # The literal sampling parameter in the disjoint recovery argument -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointRecoveryParameters

def parameter (d t : ℕ) : ℝ := (t : ℝ) ^ (-(1 : ℝ) / (d : ℝ))

theorem parameter_pos (d t : ℕ) (ht : 2 ≤ t) : 0 < parameter d t :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < t)) _

theorem parameter_lt_one (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) : parameter d t < 1 := by
  have htone : (1 : ℝ) < t := by exact_mod_cast (by omega : 1 < t)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact Real.rpow_lt_one_of_one_lt_of_neg htone (div_neg_of_neg_of_pos (by norm_num) hdpos)

theorem parameter_pow (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    parameter d t ^ d = (t : ℝ)⁻¹ := by
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  unfold parameter
  rw [← Real.rpow_mul_natCast htpos.le]
  rw [div_mul_cancel₀ _ hdne, Real.rpow_neg_one]

theorem one_sub_inv_pow_le_half (t : ℕ) (ht : 2 ≤ t) :
    (1 - (t : ℝ)⁻¹) ^ t ≤ (1 : ℝ) / 2 := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have htone : (1 : ℝ) < t := by exact_mod_cast (by omega : 1 < t)
  have hmpos : (0 : ℝ) < (t : ℝ) - 1 := by linarith
  have hb : 0 ≤ ((t : ℝ) - 1)⁻¹ := inv_nonneg.mpr hmpos.le
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ ((t : ℝ) - 1)⁻¹ by linarith) t
  have hratio : (1 : ℝ) ≤ (t : ℝ) * ((t : ℝ) - 1)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hmpos).mpr (by linarith)
  have htwo : (2 : ℝ) ≤ (1 + ((t : ℝ) - 1)⁻¹) ^ t := by linarith
  have hq : 0 ≤ 1 - (t : ℝ)⁻¹ := by
    have h := (inv_le_one₀ htpos).mpr htone.le
    linarith
  have hfactor : (1 - (t : ℝ)⁻¹) * (1 + ((t : ℝ) - 1)⁻¹) = 1 := by
    field_simp
    ring
  have hproduct : (1 - (t : ℝ)⁻¹) ^ t * (1 + ((t : ℝ) - 1)⁻¹) ^ t = 1 := by
    rw [← mul_pow, hfactor, one_pow]
  have hscaled := mul_le_mul_of_nonneg_left htwo (pow_nonneg hq t)
  nlinarith

theorem failure_factor_le_half (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    (1 - parameter d t ^ d) ^ t ≤ (1 : ℝ) / 2 := by
  rw [parameter_pow d t hd ht]
  exact one_sub_inv_pow_le_half t ht

end PaperP1.DisjointRecoveryParameters
