module

public import PaperP1.Algebra.QuadraticMomentRecurrence

/-! # Finite quantitative control of every cumulant from quadratic moment data and a squared small parameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticCumulantBound

open Finset PowerSeries PaperP1.FormalFactorialCumulants PaperP1.QuadraticMomentRecurrence

structure Data (f : ℝ⟦X⟧) (μ a M τ : ℝ) (R : ℕ) : Prop where
  constant : constantCoeff f = 1
  mean : moment f 1 = μ
  second : cumulant f 2 = a
  mean_nonneg : 0 ≤ μ
  mean_le : μ ≤ M
  error_nonneg : 0 ≤ τ
  error_le_one : τ ≤ 1
  square_le : a ^ 2 ≤ τ
  errors : ∀ j : ℕ, j ≤ R → |moment f j - quadratic μ a j| ≤ τ

def envelope (M : ℝ) (j : ℕ) : ℝ := M ^ j + (j.choose 2 : ℝ) * M ^ (j - 2) + 1

def curvature (M : ℝ) (n : ℕ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * ((n - 2).choose 2 : ℝ) * M ^ (n - 4)

def budget (M : ℝ) (K : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + M + ((n - 1 : ℕ) : ℝ) + curvature M n +
    ∑ i ∈ Icc 2 (n - 2), ((n - 1).choose i : ℝ) * K i * envelope M (n - 1 - i)

theorem Data.mono {f : ℝ⟦X⟧} {μ a M τ : ℝ} {R S : ℕ} (d : Data f μ a M τ R) (h : S ≤ R) :
    Data f μ a M τ S :=
  ⟨d.constant, d.mean, d.second, d.mean_nonneg, d.mean_le, d.error_nonneg, d.error_le_one,
    d.square_le, fun j hj ↦ d.errors j (hj.trans h)⟩

theorem Data.parameter_bound {f : ℝ⟦X⟧} {μ a M τ : ℝ} {R : ℕ} (d : Data f μ a M τ R) : |a| ≤ 1 := by
  have h : |a| ^ 2 ≤ 1 := by rw [sq_abs]; exact d.square_le.trans d.error_le_one
  nlinarith only [h, abs_nonneg a]

theorem Data.moment_bound {f : ℝ⟦X⟧} {μ a M τ : ℝ} {R : ℕ} (d : Data f μ a M τ R)
    (j : ℕ) (hj : j ≤ R) : |moment f j| ≤ envelope M j :=
  QuadraticMomentRecurrence.moment_bound f μ a M τ d.mean_nonneg d.mean_le d.parameter_bound
    d.error_le_one j (d.errors j hj)

theorem envelope_nonneg (M : ℝ) (hM : 0 ≤ M) (j : ℕ) : 0 ≤ envelope M j := by
  dsimp only [envelope]
  positivity

theorem curvature_nonneg (M : ℝ) (hM : 0 ≤ M) (n : ℕ) : 0 ≤ curvature M n := by
  dsimp only [curvature]
  positivity

theorem budget_nonneg (M : ℝ) (hM : 0 ≤ M) (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i) (n : ℕ) :
    0 ≤ budget M K n := by
  dsimp only [budget]
  exact add_nonneg (by have h := curvature_nonneg M hM n; positivity)
    (sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK i)) (envelope_nonneg M hM _))

theorem step_bound (f : ℝ⟦X⟧) (μ a M τ : ℝ) (n : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (d : Data f μ a M τ n) (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hprior : ∀ i ∈ Icc 2 (n - 2), |cumulant f (i + 1)| ≤ K i * τ) :
    |cumulant f n| ≤ budget M K n * τ := by
  let E := fun j ↦ moment f j - quadratic μ a j
  let Q := quadratic μ a n - μ * quadratic μ a (n - 1) -
    ((n - 1 : ℕ) : ℝ) * a * quadratic μ a (n - 2)
  let S := ∑ i ∈ Icc 2 (n - 2), ((n - 1).choose i : ℝ) * cumulant f (i + 1) * moment f (n - 1 - i)
  have hid : cumulant f n = E n - μ * E (n - 1) - ((n - 1 : ℕ) : ℝ) * a * E (n - 2) + Q - S := by
    rw [cumulant_recurrence f d.constant n hn, d.mean, d.second]
    dsimp only [E, Q, S]
    ring
  have hE : |E n| ≤ τ := d.errors n le_rfl
  have hE1 : |μ * E (n - 1)| ≤ M * τ := by
    rw [abs_mul, abs_of_nonneg d.mean_nonneg]
    exact mul_le_mul d.mean_le (d.errors (n - 1) (Nat.sub_le _ _)) (abs_nonneg _)
      ((by norm_num : (0 : ℝ) ≤ 1).trans hM)
  have hE2 : |((n - 1 : ℕ) : ℝ) * a * E (n - 2)| ≤ ((n - 1 : ℕ) : ℝ) * τ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hleft : ((n - 1 : ℕ) : ℝ) * |a| ≤ ((n - 1 : ℕ) : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left d.parameter_bound (Nat.cast_nonneg _)
    exact mul_le_mul hleft (d.errors (n - 2) (Nat.sub_le _ _)) (abs_nonneg _) (Nat.cast_nonneg _)
  have hQ : |Q| ≤ curvature M n * τ :=
    residual_bound μ a M τ d.mean_nonneg d.mean_le ((by norm_num : (0 : ℝ) ≤ 1).trans hM) d.square_le n hn
  have hS : |S| ≤ (∑ i ∈ Icc 2 (n - 2), ((n - 1).choose i : ℝ) * K i * envelope M (n - 1 - i)) * τ := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hterm := mul_le_mul
      (mul_le_mul_of_nonneg_left (hprior i hi) (Nat.cast_nonneg ((n - 1).choose i)))
      (d.moment_bound (n - 1 - i) ((Nat.sub_le _ _).trans (Nat.sub_le _ _)))
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK i) d.error_nonneg))
    exact hterm.trans_eq (by ring)
  have htriangle : |E n - μ * E (n - 1) - ((n - 1 : ℕ) : ℝ) * a * E (n - 2) + Q - S| ≤
      |E n| + |μ * E (n - 1)| + |((n - 1 : ℕ) : ℝ) * a * E (n - 2)| + |Q| + |S| := by
    have h0 := abs_sub (E n) (μ * E (n - 1))
    have h1 := abs_sub (E n - μ * E (n - 1)) (((n - 1 : ℕ) : ℝ) * a * E (n - 2))
    have h2 := abs_add_le (E n - μ * E (n - 1) - ((n - 1 : ℕ) : ℝ) * a * E (n - 2)) Q
    have h3 := abs_sub (E n - μ * E (n - 1) - ((n - 1 : ℕ) : ℝ) * a * E (n - 2) + Q) S
    linarith only [h0, h1, h2, h3]
  rw [hid]
  calc
    _ ≤ |E n| + |μ * E (n - 1)| + |((n - 1 : ℕ) : ℝ) * a * E (n - 2)| + |Q| + |S| := htriangle
    _ ≤ τ + M * τ + ((n - 1 : ℕ) : ℝ) * τ + curvature M n * τ +
        (∑ i ∈ Icc 2 (n - 2), ((n - 1).choose i : ℝ) * K i * envelope M (n - 1 - i)) * τ :=
      add_le_add (add_le_add (add_le_add (add_le_add hE hE1) hE2) hQ) hS
    _ = _ := by dsimp only [budget]; ring

end PaperP1.QuadraticCumulantBound
