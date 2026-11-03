module

public import PaperP1.Algebra.FormalFactorialCumulants
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Positivity

/-! # The exact residual in the quadratic factorial-moment recurrence is second order in the quadratic parameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticMomentRecurrence

open Finset PowerSeries PaperP1.FormalFactorialCumulants

def quadratic (μ a : ℝ) (r : ℕ) : ℝ := μ ^ r + (r.choose 2 : ℝ) * μ ^ (r - 2) * a

theorem quadratic_zero (μ a : ℝ) : quadratic μ a 0 = 1 := by norm_num [quadratic]

theorem quadratic_one (μ a : ℝ) : quadratic μ a 1 = μ := by norm_num [quadratic]

theorem quadratic_two (μ a : ℝ) : quadratic μ a 2 = μ ^ 2 + a := by norm_num [quadratic]

theorem recurrence_three (μ a : ℝ) :
    quadratic μ a 3 - μ * quadratic μ a 2 - 2 * a * quadratic μ a 1 = 0 := by
  norm_num [quadratic]
  ring

theorem recurrence_four (μ a : ℝ) (n : ℕ) :
    quadratic μ a (n + 4) - μ * quadratic μ a (n + 3) - (n + 3 : ℝ) * a * quadratic μ a (n + 2) =
      -(n + 3 : ℝ) * ((n + 2).choose 2 : ℝ) * μ ^ n * a ^ 2 := by
  unfold quadratic
  rw [show n + 4 - 2 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega, Nat.add_sub_cancel]
  simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat, pow_add]
  ring

theorem cumulant_recurrence (f : ℝ⟦X⟧) (hf : PowerSeries.constantCoeff f = 1) (n : ℕ) (hn : 3 ≤ n) :
    cumulant f n = moment f n - moment f 1 * moment f (n - 1) -
      ((n - 1 : ℕ) : ℝ) * cumulant f 2 * moment f (n - 2) -
      ∑ i ∈ Icc 2 (n - 2), ((n - 1).choose i : ℝ) * cumulant f (i + 1) * moment f (n - 1 - i) := by
  let F := fun i ↦ ((n - 1).choose i : ℝ) * cumulant f (i + 1) * moment f (n - 1 - i)
  have h := FormalFactorialCumulants.recurrence f hf (n - 1)
  rw [show n - 1 + 1 = n by omega] at h
  have hs := sum_range_add_sum_Ico F (show 2 ≤ n - 1 by omega)
  have hinterval : Ico 2 (n - 1) = Icc 2 (n - 2) := by ext i; simp only [mem_Ico, mem_Icc]; omega
  change cumulant f n = moment f n - ∑ i ∈ range (n - 1), F i at h
  rw [← hs, hinterval] at h
  have hfirst : (∑ i ∈ range 2, F i) = moment f 1 * moment f (n - 1) +
      ((n - 1 : ℕ) : ℝ) * cumulant f 2 * moment f (n - 2) := by
    simp only [sum_range_succ, sum_range_zero, zero_add, F, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, one_mul, Nat.reduceAdd, Nat.sub_sub,
      cumulant_one f hf]
  rw [hfirst] at h
  dsimp only [F] at h
  linarith only [h]

theorem quadratic_bound (μ a M : ℝ) (hμ : 0 ≤ μ) (hμM : μ ≤ M) (ha : |a| ≤ 1) (r : ℕ) :
    |quadratic μ a r| ≤ M ^ r + (r.choose 2 : ℝ) * M ^ (r - 2) := by
  have hterm : |(r.choose 2 : ℝ) * μ ^ (r - 2) * a| ≤ (r.choose 2 : ℝ) * M ^ (r - 2) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hμ _))]
    calc
      _ ≤ (r.choose 2 : ℝ) * μ ^ (r - 2) * 1 := mul_le_mul_of_nonneg_left ha (by positivity)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ hμM _) (Nat.cast_nonneg _)
  exact (abs_add_le _ _).trans
    (add_le_add (by simpa only [abs_of_nonneg (pow_nonneg hμ r)] using pow_le_pow_left₀ hμ hμM r) hterm)

theorem moment_bound (f : ℝ⟦X⟧) (μ a M τ : ℝ) (hμ : 0 ≤ μ) (hμM : μ ≤ M)
    (ha : |a| ≤ 1) (hτ : τ ≤ 1) (r : ℕ) (herr : |moment f r - quadratic μ a r| ≤ τ) :
    |moment f r| ≤ M ^ r + (r.choose 2 : ℝ) * M ^ (r - 2) + 1 := by
  have htriangle : |moment f r| ≤ |moment f r - quadratic μ a r| + |quadratic μ a r| := by
    convert abs_sub_le (moment f r) (quadratic μ a r) 0 using 1 <;> simp only [sub_zero]
  have hq := quadratic_bound μ a M hμ hμM ha r
  linarith only [htriangle, herr, hτ, hq]

theorem residual_bound (μ a M τ : ℝ) (hμ : 0 ≤ μ) (hμM : μ ≤ M) (hM : 0 ≤ M)
    (ha : a ^ 2 ≤ τ) (n : ℕ) (hn : 3 ≤ n) :
    |quadratic μ a n - μ * quadratic μ a (n - 1) - ((n - 1 : ℕ) : ℝ) * a * quadratic μ a (n - 2)| ≤
      (((n - 1 : ℕ) : ℝ) * ((n - 2).choose 2 : ℝ) * M ^ (n - 4)) * τ := by
  by_cases hnthree : n = 3
  · subst n
    simpa only [Nat.reduceSub, Nat.cast_ofNat, recurrence_three, abs_zero,
      Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero, mul_zero, zero_mul] using (le_refl (0 : ℝ))
  have hn4 : 4 ≤ n := by omega
  let m := n - 4
  have hnm : n = m + 4 := by dsimp [m]; omega
  rw [hnm, show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 4 = m by omega, Nat.cast_add, Nat.cast_ofNat, recurrence_four]
  have hcoef : 0 ≤ (m + 3 : ℝ) * ((m + 2).choose 2 : ℝ) := by positivity
  have hnonneg : 0 ≤ (m + 3 : ℝ) * ((m + 2).choose 2 : ℝ) * μ ^ m * a ^ 2 := by positivity
  have habs : |-(m + 3 : ℝ) * ((m + 2).choose 2 : ℝ) * μ ^ m * a ^ 2| =
      (m + 3 : ℝ) * ((m + 2).choose 2 : ℝ) * μ ^ m * a ^ 2 := by
    rw [show -(m + 3 : ℝ) * ((m + 2).choose 2 : ℝ) * μ ^ m * a ^ 2 =
      -((m + 3 : ℝ) * ((m + 2).choose 2 : ℝ) * μ ^ m * a ^ 2) by ring, abs_neg, abs_of_nonneg hnonneg]
  rw [habs]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ hμM m) hcoef) ha
    (sq_nonneg a) (mul_nonneg hcoef (pow_nonneg hM _))

end PaperP1.QuadraticMomentRecurrence
