module

public import PaperP1.Arithmetic.PrimeSetEuler
public import PaperP1.Arithmetic.WeightedPrimeSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The logarithmic gain in a finite prime-cardinality Euler bound

Splitting at `m * log (m + 2)` gives the cardinality estimate needed for
growing-order exposure. The proof uses the elementary weighted prime sum,
not an unproved estimate for the nth prime.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCardinalityEuler

open Finset PaperP1.DefectCounting PaperP1.WeightedPrimeSum
  PaperP1.SmoothSquarefreeCount

def constant : ℝ := 2 * smallPrimeConstant + 8

theorem constant_ge_eight : 8 ≤ constant := by
  have h : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold constant smallPrimeConstant
  linarith

theorem constant_pos : 0 < constant := by linarith [constant_ge_eight]

theorem log_shift_pos (m : ℕ) : 0 < Real.log ((m : ℝ) + 2) :=
  Real.log_pos (by have h : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)

theorem log_shift_ge_one {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ Real.log ((m : ℝ) + 2) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hfour : (4 : ℝ) ≤ (m : ℝ) + 2 := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hfour
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlogfour] at hlog
  linarith [Real.log_two_gt_d9]

theorem split_log_lower {m : ℕ} (hm : 2 ≤ m) :
    Real.log ((m : ℝ) + 2) / 2 ≤
      Real.log ((m : ℝ) * Real.log ((m : ℝ) + 2)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hl := log_shift_ge_one hm
  have hlog : Real.log ((m : ℝ) + 2) ≤ 2 * Real.log m := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < m + 2)
      (by nlinarith : (m : ℝ) + 2 ≤ (m : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [Real.log_mul hm0.ne' (by linarith : Real.log ((m : ℝ) + 2) ≠ 0)]
  have hll := Real.log_nonneg hl
  linarith

theorem sqrt_split_identity {m : ℕ} (hm : 0 < m) :
    Real.sqrt ((m : ℝ) * Real.log ((m : ℝ) + 2)) =
      Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2)) * Real.log ((m : ℝ) + 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl := log_shift_pos m
  have hsq := Real.sq_sqrt (div_nonneg hm0.le hl.le)
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  field_simp [hl.ne'] at hsq ⊢
  nlinarith

theorem sum_le_of_two_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (m : ℕ) (hm : 2 ≤ m) (hcard : P.card ≤ m) :
    (∑ p ∈ P, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      (2 * smallPrimeConstant + 1) *
        Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2)) := by
  let Y : ℝ := (m : ℝ) * Real.log ((m : ℝ) + 2)
  let low := P.filter fun p ↦ p ≤ Nat.floor Y
  let high := P.filter fun p ↦ ¬p ≤ Nat.floor Y
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hl := log_shift_ge_one hm
  have hl0 := log_shift_pos m
  have hY : 1 < Y := by dsimp [Y]; nlinarith
  have hlogY := split_log_lower hm
  have hsqrt := sqrt_split_identity (by omega : 0 < m)
  have hlow : low ⊆ smallPrimesUpTo (Nat.floor Y) := by
    intro p hp
    obtain ⟨hp, hpY⟩ := mem_filter.mp hp
    exact mem_smallPrimesUpTo.mpr ⟨hP p hp, hpY⟩
  have hlow_sum : (∑ p ∈ low, (p : ℝ) ^ (-(1 / 2 : ℝ))) * Real.log Y ≤
      smallPrimeConstant * Real.sqrt Y := by
    calc
      _ ≤ primeSum (Nat.floor Y) (1 / 2) * Real.log Y :=
        mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg hlow
          (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)) (Real.log_pos hY).le
      _ ≤ _ := by
        simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
          ← Real.sqrt_eq_rpow] using
          primeSum_mul_log_le_uniform Y (1 / 2) (by linarith) (by norm_num) (by norm_num)
  have hsum0 : 0 ≤ ∑ p ∈ low, (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sum_nonneg (fun p _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hsmall0 : 0 ≤ smallPrimeConstant := by
    unfold smallPrimeConstant
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  have hlow_bound : (∑ p ∈ low, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * smallPrimeConstant * Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2)) := by
    have h := mul_le_mul_of_nonneg_left hlogY hsum0
    change _ ≤ smallPrimeConstant * Real.sqrt
      ((m : ℝ) * Real.log ((m : ℝ) + 2)) at hlow_sum
    rw [hsqrt] at hlow_sum
    nlinarith
  have hhigh_term (p : ℕ) (hp : p ∈ high) :
      (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Y ^ (-(1 / 2 : ℝ)) := by
    have hpY := (mem_filter.mp hp).2
    have hlarge : Y < (p : ℝ) := by
      by_contra h
      exact hpY ((Nat.le_floor_iff (by linarith : 0 ≤ Y)).mpr (by linarith))
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hlarge.le (by norm_num)
  have hhigh_card : (high.card : ℝ) ≤ m := by
    exact_mod_cast (card_le_card (filter_subset _ _)).trans hcard
  have hhigh_sum : (∑ p ∈ high, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      (m : ℝ) * Y ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ high, Y ^ (-(1 / 2 : ℝ)) := sum_le_sum hhigh_term
      _ = high.card * Y ^ (-(1 / 2 : ℝ)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hhigh_card (Real.rpow_nonneg (by linarith) _)
  have hhigh_bound : (∑ p ∈ high, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2)) := by
    have hroot0 := Real.sqrt_pos.mpr (div_pos hm0 hl0)
    have hroot_sq := Real.sq_sqrt (div_nonneg hm0.le hl0.le)
    have hid : (m : ℝ) * Y ^ (-(1 / 2 : ℝ)) =
        Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2)) := by
      rw [PaperP1.rpow_neg_one_half_eq_inv_sqrt Y (by linarith)]
      change (m : ℝ) * (Real.sqrt ((m : ℝ) * Real.log ((m : ℝ) + 2)))⁻¹ = _
      rw [hsqrt]
      field_simp [hroot0.ne', hl0.ne'] at hroot_sq ⊢
      nlinarith
    exact hhigh_sum.trans hid.le
  have hsplit := sum_filter_add_sum_filter_not
    P (fun p : ℕ ↦ p ≤ Nat.floor Y) (fun p : ℕ ↦ (p : ℝ) ^ (-(1 / 2 : ℝ)))
  change (∑ p ∈ low, _) + (∑ p ∈ high, _) = _ at hsplit
  rw [← hsplit]
  linarith

theorem sum_neg_half_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (m : ℕ) (hcard : P.card ≤ m) :
    (∑ p ∈ P, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      constant * Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2)) := by
  by_cases hm : 2 ≤ m
  · have h := sum_le_of_two_le P hP m hm hcard
    have hroot := Real.sqrt_nonneg ((m : ℝ) / Real.log ((m : ℝ) + 2))
    unfold constant
    nlinarith
  · by_cases hm0 : m = 0
    · have hP0 : P = ∅ := card_eq_zero.mp (by omega)
      simp [hP0, hm0]
    · have hm1 : m = 1 := by omega
      subst m
      have hcoarse := PrimeSetEuler.sum_neg_half_le P (fun p hp ↦ (hP p hp).one_lt.le)
      have hcardR : (P.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      have hsqrt := Real.sqrt_le_sqrt hcardR
      have hlog : Real.log (3 : ℝ) ≤ 4 := by
        have h := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
        linarith
      have hlog0 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
      have hquarter : (1 / 4 : ℝ) ≤ 1 / Real.log 3 :=
        (le_div_iff₀ hlog0).mpr (by linarith)
      have hroot := Real.sqrt_le_sqrt hquarter
      have hsqrt' : Real.sqrt (P.card : ℝ) ≤ 1 := by simpa only [Real.sqrt_one] using hsqrt
      have hroot' : (1 / 2 : ℝ) ≤ Real.sqrt (1 / Real.log 3) := by
        have hquarter_root : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
          apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
          norm_num
        rw [hquarter_root] at hroot
        exact hroot
      norm_num only [Nat.cast_one, one_add_one_eq_two, show (1 : ℝ) + 2 = 3 by norm_num] at ⊢
      have hconst := constant_ge_eight
      nlinarith [Real.sqrt_nonneg (1 / Real.log 3)]

theorem euler_half_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (m : ℕ) (hcard : P.card ≤ m) :
    eulerProduct P (1 / 2) ≤
      Real.exp (constant * Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2))) := by
  calc
    _ ≤ Real.exp (∑ p ∈ P, (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
      Real.prod_one_add_le_exp_sum _ (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ _ := Real.exp_le_exp.mpr (sum_neg_half_le P hP m hcard)

theorem naturalValues_card_le_sqrt_exp (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (m : ℕ) (hcard : P.card ≤ m) (X : ℕ) :
    ((naturalValues P X).card : ℝ) ≤ Real.sqrt X *
      Real.exp (constant * Real.sqrt ((m : ℝ) / Real.log ((m : ℝ) + 2))) := by
  have h := card_naturalValues_le_euler P (fun p hp ↦ (hP p hp).one_lt.le) X (1 / 2) le_rfl
  rw [← Real.sqrt_eq_rpow] at h
  exact h.trans (mul_le_mul_of_nonneg_left (euler_half_le P hP m hcard) (Real.sqrt_nonneg X))

end PaperP1.PrimeCardinalityEuler
