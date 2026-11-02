module

public import PaperP1.Analysis.BanachExponentialRemainder
public import PaperP1.Analysis.BanachPowerPerturbation

/-! # Explicit quadratic exponential approximation for heterogeneous products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteExponentialProducts

open Finset PaperP1.BanachExponentialRemainder

theorem insertion_identity {A : Type*} [CommRing A] (a d q P D Q : A) :
    a * P - d * D + (q + Q) * (d * D) =
      a * (P - D + Q * D) + (a - d + q) * D + Q * (d - a) * D + q * (d - 1) * D := by
  ring

variable {ι A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

def product (s : Finset ι) (v : ι → A) : A := ∏ i ∈ s, (1 + v i)

def exponentialProduct (s : Finset ι) (v : ι → A) : A := ∏ i ∈ s, NormedSpace.exp (v i)

def quadraticCorrection (s : Finset ι) (v : ι → A) : A := ∑ i ∈ s, (1 / 2 : ℝ) • (v i) ^ 2

omit [CompleteSpace A] in
theorem norm_half_square_le (v : A) : ‖(1 / 2 : ℝ) • v ^ 2‖ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  rw [norm_smul]
  norm_num
  exact norm_pow_le v 2

omit [CompleteSpace A] [NormedAlgebra ℝ A] in
theorem norm_one_add_le (v : A) : ‖1 + v‖ ≤ Real.exp ‖v‖ := by
  have h := norm_add_le (1 : A) v
  rw [norm_one] at h
  exact h.trans (by simpa only [add_comm] using Real.add_one_le_exp ‖v‖)

theorem norm_local_quadratic_le (v : A) :
    ‖1 + v - NormedSpace.exp v + (1 / 2 : ℝ) • v ^ 2‖ ≤ ‖v‖ ^ 3 * Real.exp ‖v‖ := by
  have hid : 1 + v - NormedSpace.exp v + (1 / 2 : ℝ) • v ^ 2 =
      -(NormedSpace.exp v - (1 + v + (1 / 2 : ℝ) • v ^ 2)) := by abel
  rw [hid, norm_neg]
  exact norm_exp_sub_quadratic_le v

theorem norm_exponentialProduct_le (s : Finset ι) (v : ι → A) :
    ‖exponentialProduct s v‖ ≤ Real.exp (∑ i ∈ s, ‖v i‖) := by
  classical
  calc
    _ ≤ ∏ i ∈ s, ‖NormedSpace.exp (v i)‖ := norm_prod_le _ _
    _ ≤ ∏ i ∈ s, Real.exp ‖v i‖ := by
      gcongr with i hi
      exact norm_exp_le (v i)
    _ = _ := (Real.exp_sum _ _).symm

omit [CompleteSpace A] in
theorem norm_quadraticCorrection_le (s : Finset ι) (v : ι → A) :
    ‖quadraticCorrection s v‖ ≤ (1 / 2 : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, ‖(1 / 2 : ℝ) • (v i) ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (1 / 2 : ℝ) * ‖v i‖ ^ 2 := sum_le_sum (fun _ _ ↦ norm_half_square_le _)
    _ = _ := (mul_sum _ _ _).symm

theorem norm_first_order_le (s : Finset ι) (v : ι → A) :
    ‖product s v - exponentialProduct s v‖ ≤
      (∑ i ∈ s, ‖v i‖ ^ 2) * Real.exp (∑ i ∈ s, ‖v i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product, exponentialProduct]
  | @insert a s ha ih =>
    let P := product s v
    let D := exponentialProduct s v
    let r := ‖v a‖
    let R := ∑ i ∈ s, ‖v i‖
    let S := ∑ i ∈ s, ‖v i‖ ^ 2
    have hS : 0 ≤ S := sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have he : ‖1 + v a - NormedSpace.exp (v a)‖ ≤ r ^ 2 * Real.exp r := by
      rw [norm_sub_rev]
      exact norm_exp_sub_linear_le _
    have h₁ : ‖(1 + v a) * (P - D)‖ ≤ Real.exp r * (S * Real.exp R) := by
      exact (norm_mul_le _ _).trans (mul_le_mul (norm_one_add_le _) ih (norm_nonneg _) (Real.exp_pos _).le)
    have h₂ : ‖(1 + v a - NormedSpace.exp (v a)) * D‖ ≤ r ^ 2 * Real.exp r * Real.exp R := by
      exact (norm_mul_le _ _).trans (mul_le_mul he (norm_exponentialProduct_le s v)
        (norm_nonneg _) (by positivity))
    simp only [product, exponentialProduct, prod_insert ha, sum_insert ha]
    change ‖(1 + v a) * P - NormedSpace.exp (v a) * D‖ ≤ (r ^ 2 + S) * Real.exp (r + R)
    have hid : (1 + v a) * P - NormedSpace.exp (v a) * D =
        (1 + v a) * (P - D) + (1 + v a - NormedSpace.exp (v a)) * D := by ring
    rw [hid]
    have h := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    rw [Real.exp_add]
    convert h using 1; ring

theorem norm_quadratic_error_le (s : Finset ι) (v : ι → A) :
    ‖product s v - exponentialProduct s v + quadraticCorrection s v * exponentialProduct s v‖ ≤
      (2 * (∑ i ∈ s, ‖v i‖ ^ 3) + (∑ i ∈ s, ‖v i‖ ^ 2) ^ 2) *
        Real.exp (∑ i ∈ s, ‖v i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product, exponentialProduct, quadraticCorrection]
  | @insert a s ha ih =>
    let P := product s v
    let D := exponentialProduct s v
    let Q := quadraticCorrection s v
    let q := (1 / 2 : ℝ) • (v a) ^ 2
    let d := NormedSpace.exp (v a)
    let r := ‖v a‖
    let R := ∑ i ∈ s, ‖v i‖
    let S := ∑ i ∈ s, ‖v i‖ ^ 2
    let T := ∑ i ∈ s, ‖v i‖ ^ 3
    have hr : 0 ≤ r := norm_nonneg _
    have hS : 0 ≤ S := sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have hT : 0 ≤ T := sum_nonneg (fun _ _ ↦ by positivity)
    have hD : ‖D‖ ≤ Real.exp R := norm_exponentialProduct_le s v
    have hQ : ‖Q‖ ≤ (1 / 2 : ℝ) * S := norm_quadraticCorrection_le s v
    have hq : ‖q‖ ≤ (1 / 2 : ℝ) * r ^ 2 := norm_half_square_le _
    have he : ‖d - (1 + v a)‖ ≤ r ^ 2 * Real.exp r := norm_exp_sub_linear_le _
    have hlocal : ‖1 + v a - d + q‖ ≤ r ^ 3 * Real.exp r := norm_local_quadratic_le _
    have hd1 : ‖d - 1‖ ≤ r * Real.exp r := norm_exp_sub_one_le _
    have h₁ : ‖(1 + v a) * (P - D + Q * D)‖ ≤
        Real.exp r * ((2 * T + S ^ 2) * Real.exp R) := by
      exact (norm_mul_le _ _).trans (mul_le_mul (norm_one_add_le _) ih
        (norm_nonneg _) (Real.exp_pos _).le)
    have h₂ : ‖(1 + v a - d + q) * D‖ ≤ r ^ 3 * Real.exp r * Real.exp R := by
      exact (norm_mul_le _ _).trans (mul_le_mul hlocal hD (norm_nonneg _) (by positivity))
    have h₃ : ‖Q * (d - (1 + v a)) * D‖ ≤
        ((1 / 2 : ℝ) * S) * (r ^ 2 * Real.exp r) * Real.exp R := by
      have hQD := (norm_mul_le Q (d - (1 + v a))).trans (mul_le_mul hQ he (norm_nonneg _) (by positivity))
      exact (norm_mul_le _ _).trans (mul_le_mul hQD hD (norm_nonneg _) (by positivity))
    have h₄ : ‖q * (d - 1) * D‖ ≤ ((1 / 2 : ℝ) * r ^ 2) * (r * Real.exp r) * Real.exp R := by
      have hqd := (norm_mul_le q (d - 1)).trans (mul_le_mul hq hd1 (norm_nonneg _) (by positivity))
      exact (norm_mul_le _ _).trans (mul_le_mul hqd hD (norm_nonneg _) (by positivity))
    have hpoly : (2 * T + S ^ 2) + r ^ 3 + (1 / 2 : ℝ) * S * r ^ 2 +
        (1 / 2 : ℝ) * r ^ 3 ≤ 2 * (r ^ 3 + T) + (r ^ 2 + S) ^ 2 := by
      nlinarith only [mul_nonneg hS (sq_nonneg r), pow_nonneg hr 3, pow_nonneg hr 4]
    simp only [product, exponentialProduct, quadraticCorrection, prod_insert ha, sum_insert ha]
    change ‖(1 + v a) * P - d * D + (q + Q) * (d * D)‖ ≤
      (2 * (r ^ 3 + T) + (r ^ 2 + S) ^ 2) * Real.exp (r + R)
    rw [insertion_identity]
    calc
      _ ≤ ((‖(1 + v a) * (P - D + Q * D)‖ + ‖(1 + v a - d + q) * D‖) +
          ‖Q * (d - (1 + v a)) * D‖) + ‖q * (d - 1) * D‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (Real.exp r * ((2 * T + S ^ 2) * Real.exp R) +
          r ^ 3 * Real.exp r * Real.exp R) +
          ((1 / 2 : ℝ) * S) * (r ^ 2 * Real.exp r) * Real.exp R +
          ((1 / 2 : ℝ) * r ^ 2) * (r * Real.exp r) * Real.exp R :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
      _ ≤ _ := by
        rw [Real.exp_add]
        have h := mul_le_mul_of_nonneg_right hpoly
          (by positivity : 0 ≤ Real.exp r * Real.exp R)
        nlinarith only [h]

end PaperP1.FiniteExponentialProducts
