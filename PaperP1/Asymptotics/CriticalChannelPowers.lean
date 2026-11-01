module

public import PaperP1.Model.LocalRigidityConsequences
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Explicit word and root powers in the actual critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalChannelPowers

theorem word_upper {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 ^ L : ℝ) ≤ (2 : ℝ) ^ C * N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhigh : (L : ℝ) ≤ Real.log N / Real.log 2 + C := by have h := (abs_le.mp hband).2; linarith
  have hmul := mul_le_mul_of_nonneg_right hhigh h2.le
  rw [add_mul, div_mul_cancel₀ _ h2.ne'] at hmul
  have he := Real.exp_le_exp.mpr hmul
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_add, Real.exp_log hn] at he
  have heq : Real.exp (C * Real.log 2) = (2 : ℝ) ^ C := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  rw [heq] at he
  exact he.trans_eq (mul_comm _ _)

theorem window_root_upper {N L b : ℕ} {C : ℝ} (hN : 2 ≤ N) (hb : 0 < b)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) ≤
      (2 : ℝ) ^ ((C + 1) / b) * (N : ℝ) ^ (1 / (b : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhigh : (L : ℝ) ≤ Real.log N / Real.log 2 + C := by have h := (abs_le.mp hband).2; linarith
  have hmul := mul_le_mul_of_nonneg_right hhigh h2.le
  rw [add_mul, div_mul_cancel₀ _ h2.ne'] at hmul
  have hdiv := div_le_div_of_nonneg_right
    (by nlinarith only [hmul] : Real.log 2 * (L : ℝ) + Real.log 2 ≤ Real.log N + Real.log 2 * (C + 1)) hbR.le
  have hlog : Real.log 2 * (((L + 1 : ℕ) : ℝ) / b) ≤
      Real.log 2 * ((C + 1) / b) + Real.log N * (1 / (b : ℝ)) := by
    convert hdiv using 1 <;> push_cast <;> ring
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hlog

theorem nominal_square_upper {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ) := by
  have hp := PaperP1.LocalRigidityConsequences.nominal_marginal_bound hN hband
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 ^ L : ℝ)⁻¹) hp 2
  rw [div_pow] at hs
  rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_two, ← div_eq_mul_inv]
  exact hs

theorem nominal_lower {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    ((2 : ℝ) ^ C)⁻¹ / N ≤ (2 ^ L : ℝ)⁻¹ := by
  calc
    _ = 1 / ((2 : ℝ) ^ C * N) := by simp only [mul_inv_rev, div_eq_mul_inv]; ring
    _ ≤ 1 / (2 ^ L : ℝ) := one_div_le_one_div_of_le (by positivity) (word_upper hN hband)
    _ = _ := by rw [one_div]

theorem nominal_square_lower {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (((2 : ℝ) ^ C)⁻¹) ^ 2 * (N : ℝ) ^ (-2 : ℝ) ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  have hp := nominal_lower hN hband
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ C)⁻¹ / N) hp 2
  rw [div_pow] at hs
  rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_two, ← div_eq_mul_inv]
  exact hs

theorem quotient_word_lower {N L b : ℕ} {C : ℝ} (hN : 2 ≤ N) (hb : 0 < b)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 : ℝ) ^ (-C / b - 1) * (N : ℝ) ^ (1 / (b : ℝ)) ≤ (2 : ℝ) ^ (L / b) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : Real.log N / Real.log 2 ≤ (L : ℝ) + C := by have h := (abs_le.mp hband).1; linarith
  have hlogN : Real.log N ≤ ((L : ℝ) + C) * Real.log 2 := (div_le_iff₀ h2).mp hlow
  have hr := Nat.mod_lt L hb
  have hid := Nat.div_add_mod L b
  have hLNat : L ≤ b * (L / b + 1) := by nlinarith only [hr, hid]
  have hLReal : (L : ℝ) ≤ (b : ℝ) * (((L / b : ℕ) : ℝ) + 1) := by exact_mod_cast hLNat
  have hLm := mul_le_mul_of_nonneg_right hLReal h2.le
  have hquot : (Real.log N - Real.log 2 * C) / b ≤ Real.log 2 * (((L / b : ℕ) : ℝ) + 1) := by
    apply (div_le_iff₀ hbR).mpr
    nlinarith only [hlogN, hLm]
  have hlog : Real.log 2 * (-C / b - 1) + Real.log N * (1 / (b : ℝ)) ≤
      Real.log 2 * ((L / b : ℕ) : ℝ) := by
    calc
      _ = (Real.log N - Real.log 2 * C) / b - Real.log 2 := by ring
      _ ≤ Real.log 2 * (((L / b : ℕ) : ℝ) + 1) - Real.log 2 := sub_le_sub_right hquot _
      _ = _ := by ring
  have heq : (2 : ℝ) ^ (L / b) = Real.exp (Real.log 2 * ((L / b : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [heq, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hlog

theorem quotient_word_upper {N L b : ℕ} {C : ℝ} (hN : 2 ≤ N) (hb : 0 < b)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 : ℝ) ^ (L / b) ≤ (2 : ℝ) ^ ((C + 1) / b) * (N : ℝ) ^ (1 / (b : ℝ)) := by
  have hdiv : ((L / b : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b := by
    apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).mpr
    have hnat : L / b * b ≤ L + 1 := (Nat.div_mul_le_self L b).trans (Nat.le_succ L)
    exact_mod_cast hnat
  calc
    _ = (2 : ℝ) ^ ((L / b : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv
    _ ≤ _ := window_root_upper hN hb hband

end PaperP1.CriticalChannelPowers
