module

public import PaperP1.Algebra.BivariateHeight
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Finset.NatAntidiagonal

/-! # Finite coefficient bounds for integer univariate and bivariate arithmetic -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialHeightArithmetic

open Finset Polynomial PaperP1.BivariateDegrees

theorem integer_height_le (p : ℤ[X]) (H : ℕ) (h : ∀ n, (p.coeff n).natAbs ≤ H) :
    integerPolynomialHeight p ≤ H := Finset.sup_le (fun n _ ↦ h n)

theorem integer_height_add (p q : ℤ[X]) :
    integerPolynomialHeight (p + q) ≤ integerPolynomialHeight p + integerPolynomialHeight q := by
  apply integer_height_le
  intro n
  rw [coeff_add]
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add
    (coeff_natAbs_le_integerPolynomialHeight p n) (coeff_natAbs_le_integerPolynomialHeight q n))

theorem integer_height_neg (p : ℤ[X]) : integerPolynomialHeight (-p) = integerPolynomialHeight p := by
  simp only [integerPolynomialHeight, support_neg, coeff_neg, Int.natAbs_neg]

theorem integer_height_sum {ι : Type*} (S : Finset ι) (f : ι → ℤ[X]) :
    integerPolynomialHeight (∑ i ∈ S, f i) ≤ ∑ i ∈ S, integerPolynomialHeight (f i) := by
  apply integer_height_le
  intro n
  rw [finsetSum_coeff]
  exact (Int.natAbs_sum_le S _).trans (sum_le_sum (fun i _ ↦ coeff_natAbs_le_integerPolynomialHeight (f i) n))

theorem coefficient_product (p q : ℤ[X]) (n : ℕ) :
    ((p * q).coeff n).natAbs ≤ (n + 1) * integerPolynomialHeight p * integerPolynomialHeight q := by
  rw [coeff_mul]
  calc
    _ ≤ ∑ i ∈ Finset.antidiagonal n, (p.coeff i.1 * q.coeff i.2).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.antidiagonal n, integerPolynomialHeight p * integerPolynomialHeight q := by
      apply sum_le_sum
      intro i _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (coeff_natAbs_le_integerPolynomialHeight p i.1)
        (coeff_natAbs_le_integerPolynomialHeight q i.2)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal, Nat.cast_id]
      ring

theorem integer_height_mul (p q : ℤ[X]) :
    integerPolynomialHeight (p * q) ≤
      (p.natDegree + q.natDegree + 1) * integerPolynomialHeight p * integerPolynomialHeight q := by
  apply Finset.sup_le
  intro n hn
  have hd : n ≤ p.natDegree + q.natDegree :=
    (le_natDegree_of_ne_zero (mem_support_iff.mp hn)).trans natDegree_mul_le
  exact (coefficient_product p q n).trans
    (Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl)

theorem integer_height_C_mul (c : ℤ) (p : ℤ[X]) :
    integerPolynomialHeight (C c * p) ≤ c.natAbs * integerPolynomialHeight p := by
  apply integer_height_le
  intro n
  rw [coeff_C_mul, Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (coeff_natAbs_le_integerPolynomialHeight p n)

theorem integer_height_X_mul (p : ℤ[X]) : integerPolynomialHeight (X * p) ≤ integerPolynomialHeight p := by
  apply integer_height_le
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul]
    exact coeff_natAbs_le_integerPolynomialHeight p n

theorem integer_height_linear_mul (c : ℤ) (p : ℤ[X]) :
    integerPolynomialHeight ((X + C c) * p) ≤ (c.natAbs + 1) * integerPolynomialHeight p := by
  rw [add_mul]
  exact (integer_height_add _ _).trans
    ((Nat.add_le_add (integer_height_X_mul p) (integer_height_C_mul c p)).trans_eq (by ring))

theorem bivariate_height_le (P : ℤ[X][X]) (H : ℕ)
    (h : ∀ i j, ((P.coeff i).coeff j).natAbs ≤ H) : BivariateHeight.height P ≤ H := by
  apply Finset.sup_le
  intro i _
  exact integer_height_le _ H (h i)

theorem row_height_le (P : ℤ[X][X]) (i : ℕ) :
    integerPolynomialHeight (P.coeff i) ≤ BivariateHeight.height P := by
  apply integer_height_le
  exact BivariateHeight.coefficient_natAbs_le_height P i

theorem bivariate_height_add (P Q : ℤ[X][X]) :
    BivariateHeight.height (P + Q) ≤ BivariateHeight.height P + BivariateHeight.height Q := by
  apply bivariate_height_le
  intro i j
  rw [coeff_add, coeff_add]
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add
    (BivariateHeight.coefficient_natAbs_le_height P i j) (BivariateHeight.coefficient_natAbs_le_height Q i j))

theorem bivariate_height_neg (P : ℤ[X][X]) : BivariateHeight.height (-P) = BivariateHeight.height P := by
  simp only [BivariateHeight.height, support_neg, coeff_neg, integer_height_neg]

theorem bivariate_height_sub (P Q : ℤ[X][X]) :
    BivariateHeight.height (P - Q) ≤ BivariateHeight.height P + BivariateHeight.height Q := by
  simpa only [sub_eq_add_neg, bivariate_height_neg] using bivariate_height_add P (-Q)

theorem bivariate_height_mul (P Q : ℤ[X][X]) :
    BivariateHeight.height (P * Q) ≤
      (degreeX P + degreeX Q + 1) * (degreeY P + degreeY Q + 1) *
        BivariateHeight.height P * BivariateHeight.height Q := by
  apply Finset.sup_le
  intro n hn
  have hd : n ≤ degreeY P + degreeY Q :=
    (le_natDegree_of_ne_zero (mem_support_iff.mp hn)).trans natDegree_mul_le
  rw [coeff_mul]
  calc
    _ ≤ ∑ i ∈ Finset.antidiagonal n, integerPolynomialHeight (P.coeff i.1 * Q.coeff i.2) :=
      integer_height_sum _ _
    _ ≤ ∑ _i ∈ Finset.antidiagonal n,
        (degreeX P + degreeX Q + 1) * BivariateHeight.height P * BivariateHeight.height Q := by
      apply sum_le_sum
      intro i _
      have hdeg : (P.coeff i.1).natDegree + (Q.coeff i.2).natDegree + 1 ≤ degreeX P + degreeX Q + 1 :=
        Nat.add_le_add_right (Nat.add_le_add (natDegree_coeff_le_degreeX P i.1)
          (natDegree_coeff_le_degreeX Q i.2)) 1
      exact (integer_height_mul _ _).trans
        (Nat.mul_le_mul (Nat.mul_le_mul hdeg (row_height_le P i.1)) (row_height_le Q i.2))
    _ = (n + 1) * (degreeX P + degreeX Q + 1) * BivariateHeight.height P * BivariateHeight.height Q := by
      simp only [sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal, Nat.cast_id]
      ring
    _ ≤ _ := by
      rw [Nat.mul_comm (n + 1) (degreeX P + degreeX Q + 1)]
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) le_rfl) le_rfl

theorem bivariate_height_scalar (n : ℕ) (P : ℤ[X][X]) :
    BivariateHeight.height ((n : ℤ[X][X]) * P) ≤ n * BivariateHeight.height P := by
  apply bivariate_height_le
  intro i j
  rw [Polynomial.coeff_natCast_mul]
  rw [Polynomial.coeff_natCast_mul, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left n (BivariateHeight.coefficient_natAbs_le_height P i j)

end PaperP1.PolynomialHeightArithmetic
