module

public import PaperP1.Arithmetic.DeterminantChartExpansion
public import PaperP1.Analysis.DeterminantRelativeChart
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The actual chart determinant reduces to a distinct weighted lattice sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantChartBound

open Finset PaperP1.DeterminantIntegerRows PaperP1.DeterminantChartExpansion
  PaperP1.WeightedEvaluationDeterminant

def weight (r₁ r₂ : ℝ) (k : ℕ × ℕ) : ℝ := Real.exp (-(r₁ * k.1 + r₂ * k.2))

def constant (A B : ℕ) : ℝ :=
  (((A + 2 * B + 1) * (B + 1) : ℕ) : ℝ) ^ ((A + 1) * (B + 1)) *
    (2 : ℝ) ^ ((A + 3 * B) * ((A + 1) * (B + 1))) *
      (((A + 1) * (B + 1)).factorial : ℝ)

def normalizedMatrix (A B : ℕ) (α β : Exponent A B → ℝ) : Matrix (Exponent A B) (Exponent A B) ℝ :=
  Matrix.of fun i j ↦ (1 + α i) ^ j.1.val * (1 + 2 * α i + α i ^ 2 + β i) ^ j.2.val

theorem monomial_bound (r₁ r₂ α β : ℝ) (hα : |α| ≤ Real.exp (-r₁))
    (hβ : |β| ≤ Real.exp (-r₂)) (k j : ℕ) : |α ^ k * β ^ j| ≤ weight r₁ r₂ (k, j) := by
  rw [abs_mul, abs_pow, abs_pow]
  calc
    _ ≤ (Real.exp (-r₁)) ^ k * (Real.exp (-r₂)) ^ j := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem weight_product {ι : Type*} [Fintype ι] (r₁ r₂ : ℝ) (f : ι → ℕ × ℕ) :
    (∏ i, weight r₁ r₂ (f i)) = Real.exp (-(∑ i, (r₁ * (f i).1 + r₂ * (f i).2))) := by
  simp only [weight, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem normalized_bound (A B : ℕ) (α β : Exponent A B → ℝ) (r₁ r₂ L : ℝ)
    (hα : ∀ i, |α i| ≤ Real.exp (-r₁)) (hβ : ∀ i, |β i| ≤ Real.exp (-r₂))
    (hcost : ∀ f : Exponent A B → Exponent (A + 2 * B) B, Function.Injective f →
      L ≤ ∑ i, (r₁ * (f i).1.val + r₂ * (f i).2.val)) :
    |(normalizedMatrix A B α β).det| ≤ constant A B * Real.exp (-L) := by
  have hm : evaluationMatrix (coefficientMatrix A B) (monomialRows A B α β) =
      (normalizedMatrix A B α β).transpose := by
    ext i j
    exact matrix_entry A B α β i j
  have hp (f : Exponent A B → Exponent (A + 2 * B) B) (hf : Function.Injective f) :
      (∏ i, weight r₁ r₂ ((f i).1.val, (f i).2.val)) ≤ Real.exp (-L) := by
    rw [weight_product]
    exact Real.exp_le_exp.mpr (neg_le_neg (hcost f hf))
  have h := weighted_bound (coefficientMatrix A B) (monomialRows A B α β)
    (fun k ↦ weight r₁ r₂ (k.1.val, k.2.val)) ((2 : ℝ) ^ (A + 3 * B)) (Real.exp (-L))
    (by positivity) (Real.exp_pos _).le (matrix_coefficient_bound A B)
    (fun k i ↦ monomial_bound r₁ r₂ (α i) (β i) (hα i) (hβ i) k.1.val k.2.val) hp
  rw [hm, Matrix.det_transpose] at h
  simpa only [Exponent, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, constant, ← pow_mul, mul_assoc] using h

theorem original_column_scaling (A B : ℕ) (s t α β : Exponent A B → ℝ) (s₀ t₀ : ℝ)
    (hs : ∀ i, s i = s₀ * (1 + α i))
    (ht : ∀ i, t i = t₀ * (1 + 2 * α i + α i ^ 2 + β i)) :
    (Matrix.of (fun i j : Exponent A B ↦ s i ^ j.1.val * t i ^ j.2.val)).det =
      (∏ j : Exponent A B, s₀ ^ j.1.val * t₀ ^ j.2.val) * (normalizedMatrix A B α β).det := by
  have hm : Matrix.of (fun i j : Exponent A B ↦ s i ^ j.1.val * t i ^ j.2.val) =
      Matrix.of (fun i j : Exponent A B ↦ (s₀ ^ j.1.val * t₀ ^ j.2.val) *
        normalizedMatrix A B α β i j) := by
    ext i j
    simp only [Matrix.of_apply, normalizedMatrix, hs, ht, mul_pow]
    ring
  rw [hm, Matrix.det_mul_row]

theorem original_bound (A B : ℕ) (s t α β : Exponent A B → ℝ) (s₀ t₀ r₁ r₂ L : ℝ)
    (hs : ∀ i, s i = s₀ * (1 + α i))
    (ht : ∀ i, t i = t₀ * (1 + 2 * α i + α i ^ 2 + β i))
    (hα : ∀ i, |α i| ≤ Real.exp (-r₁)) (hβ : ∀ i, |β i| ≤ Real.exp (-r₂))
    (hcost : ∀ f : Exponent A B → Exponent (A + 2 * B) B, Function.Injective f →
      L ≤ ∑ i, (r₁ * (f i).1.val + r₂ * (f i).2.val)) :
    |(Matrix.of (fun i j : Exponent A B ↦ s i ^ j.1.val * t i ^ j.2.val)).det| ≤
      |∏ j : Exponent A B, s₀ ^ j.1.val * t₀ ^ j.2.val| * constant A B * Real.exp (-L) := by
  rw [original_column_scaling A B s t α β s₀ t₀ hs ht, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (normalized_bound A B α β r₁ r₂ L hα hβ hcost) (abs_nonneg _)

end PaperP1.DeterminantChartBound
