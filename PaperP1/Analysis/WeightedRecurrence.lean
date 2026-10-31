module

public import PaperP1.Analysis.FactorialResolvent
public import Mathlib.Algebra.BigOperators.Field

/-! # Exact weighted recurrence and its factorial resolvent

The residual divides by the positive integer k+1. It therefore makes sense
for every summable sequence, without assuming a finite first moment.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedRecurrence

open PaperP1.FactorialResolvent Finset

def residual (μ : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := a (k + 1) - μ / (k + 1 : ℝ) * a k

def l1 (a : ℕ → ℝ) : ℝ := ∑' k, |a k|

theorem l1_nonneg (a : ℕ → ℝ) : 0 ≤ l1 a := tsum_nonneg fun _ ↦ abs_nonneg _

theorem abs_tsum_le_l1 {a : ℕ → ℝ} (ha : Summable a) : |∑' k, a k| ≤ l1 a := by
  simpa only [Real.norm_eq_abs, l1] using norm_tsum_le_tsum_norm ha.norm

theorem l1_add_le {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) :
    l1 (a + b) ≤ l1 a + l1 b := by
  have hab : Summable (fun k ↦ |a k + b k|) := by
    simpa only [Real.norm_eq_abs] using (ha.add hb).norm
  have hsa := ha.norm.hasSum
  have hsb := hb.norm.hasSum
  simp only [Real.norm_eq_abs] at hsa hsb
  exact hasSum_le (fun k ↦ abs_add_le _ _) hab.hasSum (hsa.add hsb)

@[simp] theorem l1_neg (a : ℕ → ℝ) : l1 (-a) = l1 a := by
  simp only [l1, Pi.neg_apply, abs_neg]

theorem l1_sub_comm (a b : ℕ → ℝ) : l1 (a - b) = l1 (b - a) := by
  rw [← l1_neg (b - a), neg_sub]

theorem abs_l1_sub_le {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) :
    |l1 a - l1 b| ≤ l1 (a - b) := by
  apply abs_le.mpr
  constructor
  · have h := l1_add_le (a := b - a) (b := a) (hb.sub ha) ha
    rw [sub_add_cancel, l1_sub_comm b a] at h
    linarith
  · have h := l1_add_le (a := a - b) (b := b) (ha.sub hb) hb
    rw [sub_add_cancel] at h
    linarith

theorem recurrence (μ : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    (k + 1 : ℝ) * a (k + 1) = μ * a k + (k + 1 : ℝ) * residual μ a k := by
  unfold residual
  field_simp
  ring

theorem residual_sub (μ : ℝ) (a b : ℕ → ℝ) : residual μ (a - b) = residual μ a - residual μ b := by
  funext k
  simp only [residual, Pi.sub_apply]
  ring

theorem residual_difference (μ ν : ℝ) (a b : ℕ → ℝ) :
    residual μ a - residual ν b = residual μ (a - b) +
      (fun k : ℕ ↦ (ν - μ) / (k + 1 : ℝ) * b k) := by
  funext k
  simp only [residual, Pi.sub_apply, Pi.add_apply, sub_div]
  ring

theorem factorial_solution (μ : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    (n.factorial : ℝ) * a n = μ ^ n * a 0 +
      ∑ j ∈ range n, μ ^ (n - j - 1) * ((j + 1).factorial : ℝ) * residual μ a j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : μ * (∑ j ∈ range n, μ ^ (n - j - 1) * ((j + 1).factorial : ℝ) * residual μ a j) =
        ∑ j ∈ range n, μ ^ ((n + 1) - j - 1) * ((j + 1).factorial : ℝ) * residual μ a j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hexp : (n + 1) - j - 1 = (n - j - 1) + 1 := by
        have h := mem_range.mp hj
        omega
      rw [hexp, pow_succ]
      ring
    calc
      _ = (n.factorial : ℝ) * ((n + 1 : ℝ) * a (n + 1)) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      _ = (n.factorial : ℝ) * (μ * a n + (n + 1 : ℝ) * residual μ a n) := by rw [recurrence]
      _ = μ * ((n.factorial : ℝ) * a n) + ((n + 1).factorial : ℝ) * residual μ a n := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      _ = μ * (μ ^ n * a 0 +
          ∑ j ∈ range n, μ ^ (n - j - 1) * ((j + 1).factorial : ℝ) * residual μ a j) +
            ((n + 1).factorial : ℝ) * residual μ a n := by rw [ih]
      _ = _ := by
        rw [sum_range_succ]
        simp only [Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, one_mul]
        rw [← hsum, pow_succ]
        ring

theorem correction_eq_range_sum (μ : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    correction μ b (n + 1) =
      (∑ j ∈ range (n + 1), μ ^ ((n + 1) - j - 1) * ((j + 1).factorial : ℝ) * b j) /
        ((n + 1).factorial : ℝ) := by
  rw [correction, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_div]
  apply sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  unfold term
  rw [show j + 1 + (n - j) = n + 1 by omega,
    show (n + 1) - j - 1 = n - j by omega]
  ring

theorem solution (μ : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    a n = a 0 * exponentialCoeff μ n + correction μ (residual μ a) n := by
  cases n with
  | zero => simp [exponentialCoeff, correction]
  | succ n =>
    have hf : (((n + 1).factorial : ℝ)) ≠ 0 := by positivity
    have hsol : a (n + 1) = (μ ^ (n + 1) * a 0 +
        ∑ j ∈ range (n + 1), μ ^ ((n + 1) - j - 1) * ((j + 1).factorial : ℝ) * residual μ a j) /
          ((n + 1).factorial : ℝ) := by
      apply (eq_div_iff hf).mpr
      simpa only [mul_comm] using factorial_solution μ a (n + 1)
    rw [hsol, correction_eq_range_sum, exponentialCoeff]
    ring

theorem residual_coefficient_bound (μ : ℝ) (k : ℕ) : |μ / (k + 1 : ℝ)| ≤ |μ| := by
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
  exact div_le_self (abs_nonneg μ) (by have h := Nat.cast_nonneg k (α := ℝ); linarith)

theorem summable_abs_weighted (μ : ℝ) {a : ℕ → ℝ} (ha : Summable a) :
    Summable (fun k : ℕ ↦ |μ / (k + 1 : ℝ) * a k|) := by
  have habs : Summable (fun k ↦ |a k|) := by simpa only [Real.norm_eq_abs] using ha.norm
  have hdom := habs.mul_left |μ|
  apply hdom.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
  intro k
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (residual_coefficient_bound μ k) (abs_nonneg _)

theorem summable_weighted (μ : ℝ) {a : ℕ → ℝ} (ha : Summable a) :
    Summable (fun k : ℕ ↦ μ / (k + 1 : ℝ) * a k) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using summable_abs_weighted μ ha

theorem summable_residual (μ : ℝ) {a : ℕ → ℝ} (ha : Summable a) : Summable (residual μ a) := by
  have htail : Summable (fun k ↦ a (k + 1)) := (summable_nat_add_iff 1).mpr ha
  exact htail.sub (summable_weighted μ ha)

theorem weighted_l1_bound (μ : ℝ) {a : ℕ → ℝ} (ha : Summable a) :
    l1 (fun k : ℕ ↦ μ / (k + 1 : ℝ) * a k) ≤ |μ| * l1 a := by
  have habs : HasSum (fun k ↦ |a k|) (l1 a) := by simpa only [Real.norm_eq_abs, l1] using ha.norm.hasSum
  exact hasSum_le (fun k ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (residual_coefficient_bound μ k) (abs_nonneg _))
    (summable_abs_weighted μ ha).hasSum (habs.mul_left |μ|)

theorem tail_l1_le {a : ℕ → ℝ} (ha : Summable a) : l1 (fun k ↦ a (k + 1)) ≤ l1 a := by
  have habs : Summable (fun k ↦ |a k|) := by simpa only [Real.norm_eq_abs] using ha.norm
  have h := habs.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at h
  unfold l1
  linarith [abs_nonneg (a 0)]

theorem residual_l1_bound (μ : ℝ) {a : ℕ → ℝ} (ha : Summable a) :
    l1 (residual μ a) ≤ (1 + |μ|) * l1 a := by
  have htail : Summable (fun k ↦ a (k + 1)) := (summable_nat_add_iff 1).mpr ha
  have h := l1_add_le (a := fun k ↦ a (k + 1)) (b := -(fun k : ℕ ↦ μ / (k + 1 : ℝ) * a k))
    htail (summable_weighted μ ha).neg
  rw [l1_neg] at h
  have ht := tail_l1_le ha
  have hw := weighted_l1_bound μ ha
  change l1 (residual μ a) ≤ _ at h
  nlinarith

theorem initial_abs_le_residual_l1 (μ : ℝ) (hμ : 0 ≤ μ) {a : ℕ → ℝ}
    (ha : Summable a) (hzero : (∑' k, a k) = 0) : |a 0| ≤ l1 (residual μ a) := by
  have hb := summable_residual μ ha
  have hc := (hasSum_correction μ hμ hb).summable
  have hs := ((hasSum_exponentialCoeff μ).mul_left (a 0)).add hc.hasSum
  have hsa : HasSum a (a 0 * Real.exp μ + ∑' k, correction μ (residual μ a) k) :=
    hs.congr_fun (solution μ a)
  have hz : HasSum a 0 := by simpa only [hzero] using ha.hasSum
  have hmass := hsa.unique hz
  have heq : a 0 * Real.exp μ = -(∑' k, correction μ (residual μ a) k) := by linarith
  have habs : |a 0| * Real.exp μ = |∑' k, correction μ (residual μ a) k| := by
    rw [← abs_of_pos (Real.exp_pos μ), ← abs_mul, heq, abs_neg]
  have hmean : |a 0| * Real.exp μ ≤ l1 (correction μ (residual μ a)) := by
    rw [habs]
    exact abs_tsum_le_l1 hc
  have hcost := correction_l1_bound μ hμ hb
  exact (mul_le_mul_iff_left₀ (Real.exp_pos μ)).mp (hmean.trans hcost)

theorem zero_mass_l1_bound (μ : ℝ) (hμ : 0 ≤ μ) {a : ℕ → ℝ}
    (ha : Summable a) (hzero : (∑' k, a k) = 0) :
    l1 a ≤ 2 * Real.exp μ * l1 (residual μ a) := by
  have hb := summable_residual μ ha
  have hcabs := summable_abs_correction μ hμ hb
  have hasa : HasSum (fun k ↦ |a k|) (l1 a) := by
    simpa only [Real.norm_eq_abs, l1] using ha.norm.hasSum
  have hpoint (k : ℕ) : |a k| ≤ |a 0| * exponentialCoeff μ k + |correction μ (residual μ a) k| := by
    rw [solution μ a k]
    have h := abs_add_le (a 0 * exponentialCoeff μ k) (correction μ (residual μ a) k)
    rwa [abs_mul, abs_of_nonneg (exponentialCoeff_nonneg μ hμ k)] at h
  have hdom := ((hasSum_exponentialCoeff μ).mul_left |a 0|).add hcabs.hasSum
  have h := hasSum_le hpoint hasa hdom
  have hinit := initial_abs_le_residual_l1 μ hμ ha hzero
  have hcost := correction_l1_bound μ hμ hb
  have hmul := mul_le_mul_of_nonneg_right hinit (Real.exp_pos μ).le
  dsimp [l1] at h hinit hmul ⊢
  nlinarith

end PaperP1.WeightedRecurrence
