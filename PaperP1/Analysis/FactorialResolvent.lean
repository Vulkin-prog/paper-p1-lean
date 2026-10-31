module

public import PaperP1.Probability.PoissonSequence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Choose.Basic

/-! # An absolutely summable factorial resolvent kernel

The inverse recurrence coefficients are bounded by the exponential series.
All double-series regroupings below have proved absolute convergence.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialResolvent

open Finset

def exponentialCoeff (μ : ℝ) (n : ℕ) : ℝ := μ ^ n / (n.factorial : ℝ)

def term (μ : ℝ) (b : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  b p.1 * μ ^ p.2 * ((p.1 + 1).factorial : ℝ) / ((p.1 + 1 + p.2).factorial : ℝ)

def correction (μ : ℝ) (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => ∑ p ∈ antidiagonal k, term μ b p

theorem hasSum_exponentialCoeff (μ : ℝ) : HasSum (exponentialCoeff μ) (Real.exp μ) := by
  have h : HasSum (fun n : ℕ ↦ μ ^ n / (n.factorial : ℝ)) (Real.exp μ) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp μ
  exact h.congr_fun fun _ ↦ rfl

theorem exponentialCoeff_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (n : ℕ) : 0 ≤ exponentialCoeff μ n := by
  unfold exponentialCoeff
  positivity

theorem factorial_ratio_bound (j n : ℕ) :
    ((j + 1).factorial : ℝ) / ((j + 1 + n).factorial : ℝ) ≤ 1 / (n.factorial : ℝ) := by
  have hnat : (j + 1).factorial * n.factorial ≤ (j + 1 + n).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using (by exact_mod_cast hnat :
    ((j + 1).factorial : ℝ) * (n.factorial : ℝ) ≤ ((j + 1 + n).factorial : ℝ))

theorem abs_term_bound (μ : ℝ) (hμ : 0 ≤ μ) (b : ℕ → ℝ) (p : ℕ × ℕ) :
    |term μ b p| ≤ |b p.1| * exponentialCoeff μ p.2 := by
  unfold term exponentialCoeff
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hμ, Nat.abs_cast, Nat.abs_cast]
  have hnonneg : 0 ≤ |b p.1| * μ ^ p.2 := mul_nonneg (abs_nonneg _) (pow_nonneg hμ _)
  have h := mul_le_mul_of_nonneg_left (factorial_ratio_bound p.1 p.2) hnonneg
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using h

theorem summable_abs_term (μ : ℝ) (hμ : 0 ≤ μ) {b : ℕ → ℝ} (hb : Summable b) :
    Summable (fun p : ℕ × ℕ ↦ |term μ b p|) := by
  have habs : Summable (fun j ↦ |b j|) := by simpa only [Real.norm_eq_abs] using hb.norm
  have hprod := habs.mul_of_nonneg (hasSum_exponentialCoeff μ).summable
    (fun j ↦ abs_nonneg (b j)) (exponentialCoeff_nonneg μ hμ)
  exact hprod.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (abs_term_bound μ hμ b)

theorem summable_term (μ : ℝ) (hμ : 0 ≤ μ) {b : ℕ → ℝ} (hb : Summable b) :
    Summable (term μ b) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using summable_abs_term μ hμ hb

theorem tsum_abs_term_bound (μ : ℝ) (hμ : 0 ≤ μ) {b : ℕ → ℝ} (hb : Summable b) :
    (∑' p : ℕ × ℕ, |term μ b p|) ≤ (∑' j, |b j|) * Real.exp μ := by
  have habs : Summable (fun j ↦ |b j|) := by simpa only [Real.norm_eq_abs] using hb.norm
  have hprod := habs.mul_of_nonneg (hasSum_exponentialCoeff μ).summable
    (fun j ↦ abs_nonneg (b j)) (exponentialCoeff_nonneg μ hμ)
  exact hasSum_le (abs_term_bound μ hμ b) (summable_abs_term μ hμ hb).hasSum
    (habs.hasSum.mul (hasSum_exponentialCoeff μ) hprod)

theorem hasSum_antidiagonal {F : ℕ × ℕ → ℝ} (hF : Summable F) :
    HasSum (fun k : ℕ ↦ ∑ p ∈ antidiagonal k, F p) (∑' p, F p) := by
  have hσ : HasSum (fun p : Σ k : ℕ, antidiagonal k ↦ F p.2.val) (∑' p, F p) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr hF.hasSum
  apply hσ.sigma
  intro k
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
    hasSum_fintype (fun p : antidiagonal k ↦ F p.val)

theorem hasSum_correction (μ : ℝ) (hμ : 0 ≤ μ) {b : ℕ → ℝ} (hb : Summable b) :
    HasSum (correction μ b) (∑' p, term μ b p) := by
  have h := PaperP1.PoissonSequence.hasSum_shift (hasSum_antidiagonal (summable_term μ hμ hb))
  exact h

theorem correction_abs_bound (μ : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    |correction μ b k| ≤ PaperP1.PoissonSequence.shift
      (fun n ↦ ∑ p ∈ antidiagonal n, |term μ b p|) k := by
  cases k with
  | zero => simp [correction]
  | succ k => exact abs_sum_le_sum_abs _ _

theorem summable_abs_correction (μ : ℝ) (hμ : 0 ≤ μ) {b : ℕ → ℝ} (hb : Summable b) :
    Summable (fun k ↦ |correction μ b k|) := by
  have hdom := (PaperP1.PoissonSequence.hasSum_shift
    (hasSum_antidiagonal (summable_abs_term μ hμ hb))).summable
  exact hdom.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (correction_abs_bound μ b)

theorem correction_l1_bound (μ : ℝ) (hμ : 0 ≤ μ) {b : ℕ → ℝ} (hb : Summable b) :
    (∑' k, |correction μ b k|) ≤ (∑' j, |b j|) * Real.exp μ := by
  have hdom := PaperP1.PoissonSequence.hasSum_shift
    (hasSum_antidiagonal (summable_abs_term μ hμ hb))
  have h := hasSum_le (correction_abs_bound μ b) (summable_abs_correction μ hμ hb).hasSum hdom
  exact h.trans (tsum_abs_term_bound μ hμ hb)

end PaperP1.FactorialResolvent
