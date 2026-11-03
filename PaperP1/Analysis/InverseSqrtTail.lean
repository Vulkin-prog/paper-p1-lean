module

public import PaperP1.Analysis.ReciprocalSqrtSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! # A finite inverse-three-halves tail by telescoping reciprocal square roots -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InverseSqrtTail

open Finset

theorem step (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (-3 / 2 : ℝ) ≤
      2 * ((Real.sqrt ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.sqrt n)⁻¹) := by
  let a := Real.sqrt (n : ℝ)
  let b := Real.sqrt ((n - 1 : ℕ) : ℝ)
  have ha : 0 < a := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hb : 0 < b := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n - 1 by omega))
  have hba : b ≤ a := PaperP1.sqrt_nat_sub_one_le n
  have hsq : a ^ 2 - b ^ 2 = 1 := PaperP1.sqrt_nat_sq_sub_sq_eq_one n (by omega)
  have hbound : b * (a + b) ≤ 2 * a ^ 2 := by
    have h := mul_nonneg ha.le (sub_nonneg.mpr hba)
    nlinarith only [h, hsq]
  have hprod : b * (a + b) * (a - b) = b := by
    calc
      _ = b * (a ^ 2 - b ^ 2) := by ring
      _ = _ := by rw [hsq, mul_one]
  have hcore : b ≤ 2 * (a - b) * a ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hbound (sub_nonneg.mpr hba)
    rw [hprod] at h
    nlinarith only [h]
  have heq : (n : ℝ) ^ (-3 / 2 : ℝ) = (a⁻¹) ^ 3 := by
    rw [show (-3 / 2 : ℝ) = (-(1 / 2 : ℝ)) * (3 : ℕ) by norm_num,
      Real.rpow_mul_natCast (Nat.cast_nonneg n), PaperP1.rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg n)]
  have hright : 2 * (b⁻¹ - a⁻¹) = 2 * (a - b) / (b * a) := by field_simp
  change (n : ℝ) ^ (-3 / 2 : ℝ) ≤ 2 * (b⁻¹ - a⁻¹)
  rw [heq, hright, inv_pow, ← one_div]
  apply (div_le_div_iff₀ (pow_pos ha _) (mul_pos hb ha)).mpr
  have h := mul_le_mul_of_nonneg_right hcore ha.le
  nlinarith only [h]

theorem interval_bound (Y X : ℕ) (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    (∑ n ∈ Ioc Y X, (n : ℝ) ^ (-3 / 2 : ℝ)) ≤
      2 * ((Real.sqrt Y)⁻¹ - (Real.sqrt X)⁻¹) := by
  revert hYX
  induction X with
  | zero => intro hYX; omega
  | succ X ih =>
    intro hYX
    by_cases hlast : Y = X + 1
    · subst Y
      simp
    · have hYX' : Y ≤ X := by omega
      have hset : Ioc Y (X + 1) = insert (X + 1) (Ioc Y X) := by
        ext n
        simp only [mem_Ioc, mem_insert]
        omega
      have hnot : X + 1 ∉ Ioc Y X := by simp
      rw [hset, sum_insert hnot]
      have hstep := step (X + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hstep
      calc
        _ ≤ 2 * ((Real.sqrt X)⁻¹ - (Real.sqrt (X + 1 : ℕ))⁻¹) +
            2 * ((Real.sqrt Y)⁻¹ - (Real.sqrt X)⁻¹) := add_le_add hstep (ih hYX')
        _ = _ := by ring

theorem tail_bound (Y X : ℕ) (hY : 1 ≤ Y) :
    (∑ n ∈ Ioc Y X, (n : ℝ) ^ (-3 / 2 : ℝ)) ≤ 2 / Real.sqrt Y := by
  by_cases hYX : Y ≤ X
  · have h := interval_bound Y X hY hYX
    have hnonneg : 0 ≤ (Real.sqrt X)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    change (∑ n ∈ Ioc Y X, (n : ℝ) ^ (-3 / 2 : ℝ)) ≤ 2 * (Real.sqrt Y)⁻¹
    linarith only [h, hnonneg]
  · have hempty : Ioc Y X = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      have h := mem_Ioc.mp hn
      omega
    rw [hempty, sum_empty]
    positivity

end PaperP1.InverseSqrtTail
