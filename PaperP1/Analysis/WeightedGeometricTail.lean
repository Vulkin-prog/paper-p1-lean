module

public import PaperP1.Analysis.RealSeriesEvaluation
public import Mathlib.Tactic.Linarith

/-! # A quantitative weighted geometric tail after an actual vanishing prefix -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedGeometricTail

open Finset

theorem weighted_hasSum (r : ℝ) (hr : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun n : ℕ ↦ ((n : ℝ) + 1) * r ^ n) (1 / (1 - r) ^ 2) := by
  have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr₁
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hn

theorem weighted_bound (r : ℝ) (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) :
    (∑' n : ℕ, ((n : ℝ) + 1) * r ^ n) ≤ 2 := by
  rw [(weighted_hasSum r hr (by linarith)).tsum_eq]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - r))).mpr
  nlinarith [sq_nonneg r]

theorem weighted_tail_bound (r : ℝ) (M : ℕ) (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) :
    (∑' n : ℕ, (((n + M : ℕ) : ℝ) + 1) * r ^ (n + M)) ≤ 2 * ((M : ℝ) + 1) * r ^ M := by
  have hs := (weighted_hasSum r hr (by linarith)).summable
  have htail : Summable (fun n : ℕ ↦ (((n + M : ℕ) : ℝ) + 1) * r ^ (n + M)) :=
    (summable_nat_add_iff M).mpr hs
  have hmajorant := hs.mul_left (((M : ℝ) + 1) * r ^ M)
  have hpoint : ∀ n : ℕ, (((n + M : ℕ) : ℝ) + 1) * r ^ (n + M) ≤
      (((M : ℝ) + 1) * r ^ M) * (((n : ℝ) + 1) * r ^ n) := by
    intro n
    have hc : (n : ℝ) + (M : ℝ) + 1 ≤ ((M : ℝ) + 1) * ((n : ℝ) + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    calc
      _ ≤ (((M : ℝ) + 1) * ((n : ℝ) + 1)) * r ^ (n + M) :=
        mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add] using hc) (pow_nonneg hr _)
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ ∑' n : ℕ, (((M : ℝ) + 1) * r ^ M) * (((n : ℝ) + 1) * r ^ n) :=
      Summable.tsum_le_tsum hpoint htail hmajorant
    _ = (((M : ℝ) + 1) * r ^ M) * ∑' n : ℕ, ((n : ℝ) + 1) * r ^ n := tsum_mul_left
    _ ≤ (((M : ℝ) + 1) * r ^ M) * 2 :=
      mul_le_mul_of_nonneg_left (weighted_bound r hr hrq) (mul_nonneg (by positivity) (pow_nonneg hr _))
    _ = _ := by ring

theorem vanishing_tail_bound (f : ℕ → ℝ) (C r : ℝ) (M : ℕ)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hrq : r ≤ 1 / 4)
    (hbound : ∀ n, ‖f n‖ ≤ C * ((n : ℝ) + 1) * r ^ n)
    (hzero : ∀ n, n < M → f n = 0) :
    ‖∑' n, f n‖ ≤ 2 * C * ((M : ℝ) + 1) * r ^ M := by
  have hmajorant : Summable (fun n : ℕ ↦ C * ((n : ℝ) + 1) * r ^ n) := by
    simpa only [mul_assoc] using (weighted_hasSum r hr (by linarith)).summable.mul_left C
  have hnorm := hmajorant.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hpref : ∑ n ∈ range M, f n = 0 := sum_eq_zero (fun n hn ↦ hzero n (mem_range.mp hn))
  have hsplit := Summable.sum_add_tsum_nat_add M hnorm.of_norm
  rw [hpref, zero_add] at hsplit
  have hnormTail : Summable (fun n : ℕ ↦ ‖f (n + M)‖) := (summable_nat_add_iff M).mpr hnorm
  have hmajorantTail : Summable (fun n : ℕ ↦ C * (((n + M : ℕ) : ℝ) + 1) * r ^ (n + M)) :=
    (summable_nat_add_iff M).mpr hmajorant
  rw [← hsplit]
  calc
    _ ≤ ∑' n : ℕ, ‖f (n + M)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' n : ℕ, C * (((n + M : ℕ) : ℝ) + 1) * r ^ (n + M) :=
      Summable.tsum_le_tsum (fun n ↦ hbound (n + M)) hnormTail hmajorantTail
    _ = C * ∑' n : ℕ, (((n + M : ℕ) : ℝ) + 1) * r ^ (n + M) := by
      simp only [mul_assoc]
      exact tsum_mul_left
    _ ≤ C * (2 * ((M : ℝ) + 1) * r ^ M) :=
      mul_le_mul_of_nonneg_left (weighted_tail_bound r M hr hrq) hC
    _ = _ := by ring

end PaperP1.WeightedGeometricTail
