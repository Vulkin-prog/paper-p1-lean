module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # The exact incidence slope of a binary nullity loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExponentialSupportSlope

def slope (T : ℕ) : ℝ := ((2 : ℝ) ^ (T - 1) - 1) / T

theorem slope_nonneg (T : ℕ) : 0 ≤ slope T := by
  exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (Nat.cast_nonneg T)

theorem cross_bound {t T : ℕ} (ht : 1 ≤ t) (htT : t ≤ T) :
    (T : ℝ) * ((2 : ℝ) ^ (t - 1) - 1) ≤ (t : ℝ) * ((2 : ℝ) ^ (T - 1) - 1) := by
  induction T, htT using Nat.le_induction with
  | base => rfl
  | succ n htn ih =>
    have hn : 1 ≤ n := ht.trans htn
    have hpow : (2 : ℝ) ^ (t - 1) ≤ (2 : ℝ) ^ (n - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hnext : (2 : ℝ) ^ (n + 1 - 1) = 2 * (2 : ℝ) ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
      exact mul_comm _ _
    have hmul : (2 : ℝ) ^ (n - 1) ≤ (t : ℝ) * (2 : ℝ) ^ (n - 1) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right htR (by positivity : 0 ≤ (2 : ℝ) ^ (n - 1))
    rw [hnext, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem loss_le_slope {t T : ℕ} (ht : 1 ≤ t) (htT : t ≤ T) :
    (2 : ℝ) ^ (t - 1) - 1 ≤ slope T * t := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have h := cross_bound ht htT
  unfold slope
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT).mpr
  nlinarith only [h]

theorem slope_le_source {T : ℕ} (hT : 1 ≤ T) : slope T ≤ (2 : ℝ) ^ (T - 1) := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hpow : 0 ≤ (2 : ℝ) ^ (T - 1) := by positivity
  apply (div_le_iff₀ (show (0 : ℝ) < T by linarith)).mpr
  nlinarith

end PaperP1.ExponentialSupportSlope
