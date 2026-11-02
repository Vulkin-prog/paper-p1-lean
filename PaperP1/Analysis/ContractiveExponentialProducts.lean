module

public import PaperP1.Analysis.FiniteExponentialProducts

/-! # Uniform finite-product errors for probability contractions

The constants depend on a local increment cap, not on the sum of all
increments. Actual Bernoulli and Poisson convolution factors have norm one.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContractiveExponentialProducts

open Finset PaperP1.FiniteExponentialProducts PaperP1.BanachExponentialRemainder

variable {ι A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

omit [CompleteSpace A] [NormedAlgebra ℝ A] in
theorem norm_exponentialProduct_le_one (s : Finset ι) (v : ι → A)
    (hD : ∀ i ∈ s, ‖NormedSpace.exp (v i)‖ ≤ 1) : ‖exponentialProduct s v‖ ≤ 1 := by
  calc
    _ ≤ ∏ i ∈ s, ‖NormedSpace.exp (v i)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i ∈ s, (1 : ℝ) := by gcongr with i hi; exact hD i hi
    _ = 1 := by simp

theorem norm_first_order_le (s : Finset ι) (v : ι → A) (R : ℝ) :
    (∀ i ∈ s, ‖1 + v i‖ ≤ 1) → (∀ i ∈ s, ‖NormedSpace.exp (v i)‖ ≤ 1) →
    (∀ i ∈ s, ‖v i‖ ≤ R) →
    ‖product s v - exponentialProduct s v‖ ≤ (∑ i ∈ s, ‖v i‖ ^ 2) * Real.exp R := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp [product, exponentialProduct]
  | @insert a s ha ih =>
    intro hA hD hR
    have hsA : ∀ i ∈ s, ‖1 + v i‖ ≤ 1 := fun i hi ↦ hA i (mem_insert_of_mem hi)
    have hsD : ∀ i ∈ s, ‖NormedSpace.exp (v i)‖ ≤ 1 := fun i hi ↦ hD i (mem_insert_of_mem hi)
    have hsR : ∀ i ∈ s, ‖v i‖ ≤ R := fun i hi ↦ hR i (mem_insert_of_mem hi)
    have hprev := ih hsA hsD hsR
    let P := product s v
    let D := exponentialProduct s v
    let S := ∑ i ∈ s, ‖v i‖ ^ 2
    let r := ‖v a‖
    have hDnorm : ‖D‖ ≤ 1 := norm_exponentialProduct_le_one s v hsD
    have hlocal : ‖1 + v a - NormedSpace.exp (v a)‖ ≤ r ^ 2 * Real.exp R := by
      rw [norm_sub_rev]
      exact (norm_exp_sub_linear_le _).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hR a (mem_insert_self _ _))) (sq_nonneg r))
    have h₁ : ‖(1 + v a) * (P - D)‖ ≤ S * Real.exp R := by
      exact (norm_mul_le _ _).trans (by simpa only [one_mul] using (mul_le_mul
        (hA a (mem_insert_self _ _)) hprev (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
    have h₂ : ‖(1 + v a - NormedSpace.exp (v a)) * D‖ ≤ r ^ 2 * Real.exp R := by
      exact (norm_mul_le _ _).trans (by simpa only [mul_one] using (mul_le_mul hlocal hDnorm
        (norm_nonneg _) (by positivity : 0 ≤ r ^ 2 * Real.exp R)))
    simp only [product, exponentialProduct, prod_insert ha, sum_insert ha]
    change ‖(1 + v a) * P - NormedSpace.exp (v a) * D‖ ≤ (r ^ 2 + S) * Real.exp R
    rw [show (1 + v a) * P - NormedSpace.exp (v a) * D =
      (1 + v a) * (P - D) + (1 + v a - NormedSpace.exp (v a)) * D by ring]
    have h := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    convert h using 1; ring

theorem norm_quadratic_error_le (s : Finset ι) (v : ι → A) (R : ℝ) :
    (∀ i ∈ s, ‖1 + v i‖ ≤ 1) → (∀ i ∈ s, ‖NormedSpace.exp (v i)‖ ≤ 1) →
    (∀ i ∈ s, ‖v i‖ ≤ R) →
    ‖product s v - exponentialProduct s v + quadraticCorrection s v * exponentialProduct s v‖ ≤
      (2 * (∑ i ∈ s, ‖v i‖ ^ 3) + (∑ i ∈ s, ‖v i‖ ^ 2) ^ 2) * Real.exp R := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp [product, exponentialProduct, quadraticCorrection]
  | @insert a s ha ih =>
    intro hA hD hR
    have hsA : ∀ i ∈ s, ‖1 + v i‖ ≤ 1 := fun i hi ↦ hA i (mem_insert_of_mem hi)
    have hsD : ∀ i ∈ s, ‖NormedSpace.exp (v i)‖ ≤ 1 := fun i hi ↦ hD i (mem_insert_of_mem hi)
    have hsR : ∀ i ∈ s, ‖v i‖ ≤ R := fun i hi ↦ hR i (mem_insert_of_mem hi)
    have hprev := ih hsA hsD hsR
    let P := product s v
    let D := exponentialProduct s v
    let Q := quadraticCorrection s v
    let q := (1 / 2 : ℝ) • (v a) ^ 2
    let d := NormedSpace.exp (v a)
    let r := ‖v a‖
    let S := ∑ i ∈ s, ‖v i‖ ^ 2
    let T := ∑ i ∈ s, ‖v i‖ ^ 3
    have hr : 0 ≤ r := norm_nonneg _
    have hS : 0 ≤ S := sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have hRlocal : Real.exp r ≤ Real.exp R := Real.exp_le_exp.mpr (hR a (mem_insert_self _ _))
    have hDnorm : ‖D‖ ≤ 1 := norm_exponentialProduct_le_one s v hsD
    have hQ : ‖Q‖ ≤ (1 / 2 : ℝ) * S := norm_quadraticCorrection_le s v
    have hq : ‖q‖ ≤ (1 / 2 : ℝ) * r ^ 2 := norm_half_square_le _
    have he : ‖d - (1 + v a)‖ ≤ r ^ 2 * Real.exp R :=
      (norm_exp_sub_linear_le _).trans (mul_le_mul_of_nonneg_left hRlocal (sq_nonneg r))
    have hlocal : ‖1 + v a - d + q‖ ≤ r ^ 3 * Real.exp R :=
      (norm_local_quadratic_le _).trans (mul_le_mul_of_nonneg_left hRlocal (pow_nonneg hr 3))
    have hd1 : ‖d - 1‖ ≤ r * Real.exp R :=
      (norm_exp_sub_one_le _).trans (mul_le_mul_of_nonneg_left hRlocal hr)
    have h₁ : ‖(1 + v a) * (P - D + Q * D)‖ ≤ (2 * T + S ^ 2) * Real.exp R := by
      exact (norm_mul_le _ _).trans (by simpa only [one_mul] using (mul_le_mul
        (hA a (mem_insert_self _ _)) hprev (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
    have h₂ : ‖(1 + v a - d + q) * D‖ ≤ r ^ 3 * Real.exp R := by
      exact (norm_mul_le _ _).trans (by simpa only [mul_one] using (mul_le_mul hlocal hDnorm
        (norm_nonneg _) (by positivity : 0 ≤ r ^ 3 * Real.exp R)))
    have h₃ : ‖Q * (d - (1 + v a)) * D‖ ≤ ((1 / 2 : ℝ) * S) * (r ^ 2 * Real.exp R) := by
      have hQD := (norm_mul_le _ _).trans (mul_le_mul hQ he (norm_nonneg _) (by positivity))
      exact (norm_mul_le _ _).trans (by simpa only [mul_one] using (mul_le_mul hQD hDnorm
        (norm_nonneg _) (by positivity : 0 ≤ ((1 / 2 : ℝ) * S) * (r ^ 2 * Real.exp R))))
    have h₄ : ‖q * (d - 1) * D‖ ≤ ((1 / 2 : ℝ) * r ^ 2) * (r * Real.exp R) := by
      have hqd := (norm_mul_le _ _).trans (mul_le_mul hq hd1 (norm_nonneg _) (by positivity))
      exact (norm_mul_le _ _).trans (by simpa only [mul_one] using (mul_le_mul hqd hDnorm
        (norm_nonneg _) (by positivity : 0 ≤ ((1 / 2 : ℝ) * r ^ 2) * (r * Real.exp R))))
    have hpoly : (2 * T + S ^ 2) + r ^ 3 + (1 / 2 : ℝ) * S * r ^ 2 +
        (1 / 2 : ℝ) * r ^ 3 ≤ 2 * (r ^ 3 + T) + (r ^ 2 + S) ^ 2 := by
      nlinarith only [mul_nonneg hS (sq_nonneg r), pow_nonneg hr 3, pow_nonneg hr 4]
    simp only [product, exponentialProduct, quadraticCorrection, prod_insert ha, sum_insert ha]
    change ‖(1 + v a) * P - d * D + (q + Q) * (d * D)‖ ≤
      (2 * (r ^ 3 + T) + (r ^ 2 + S) ^ 2) * Real.exp R
    rw [insertion_identity]
    have htriangle : ‖(1 + v a) * (P - D + Q * D) + (1 + v a - d + q) * D +
        Q * (d - (1 + v a)) * D + q * (d - 1) * D‖ ≤
      ((‖(1 + v a) * (P - D + Q * D)‖ + ‖(1 + v a - d + q) * D‖) +
        ‖Q * (d - (1 + v a)) * D‖) + ‖q * (d - 1) * D‖ :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    have hbound := htriangle.trans (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄)
    have hscale := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos R).le
    nlinarith only [hbound, hscale]

end PaperP1.ContractiveExponentialProducts
