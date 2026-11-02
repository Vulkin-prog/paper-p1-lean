module

public import PaperP1.Algebra.PolynomialHeightArithmetic
public import PaperP1.Algebra.FormalWordPolynomials

/-! # Finite height bounds for the actual integer word polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FormalWordHeight

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.PolynomialHeightArithmetic

theorem linear_height (I : Finset ℤ) (B : ℕ) (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) :
    integerPolynomialHeight (linearOver ℤ I) ≤ (B + 1) ^ I.card := by
  classical
  revert hI
  induction I using Finset.induction_on with
  | empty =>
    intro _
    change integerPolynomialHeight (1 : ℤ[X]) ≤ 1
    apply integer_height_le
    intro n
    rw [coeff_one]
    split_ifs <;> norm_num
  | @insert c I hc ih =>
    intro h
    have hcB : c.natAbs ≤ B := by
      rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
      exact h c (mem_insert_self c I)
    have hIB := ih (fun i hi ↦ h i (mem_insert_of_mem hi))
    change integerPolynomialHeight (∏ i ∈ insert c I, (X + C (i : ℤ))) ≤ _
    rw [prod_insert hc]
    calc
      _ ≤ (c.natAbs + 1) * integerPolynomialHeight (linearOver ℤ I) := integer_height_linear_mul c _
      _ ≤ (B + 1) * (B + 1) ^ I.card := Nat.mul_le_mul (by omega) hIB
      _ = _ := by rw [card_insert_of_notMem hc, pow_succ]; ring

theorem word_coefficient (I J : Finset ℤ) (x y : ℕ) :
    ((wordOver ℤ I J).coeff y).coeff x = (linearOver ℤ I).coeff x * (linearOver ℤ J).coeff y := by
  rw [wordOver, coeff_C_mul, coeff_map, coeff_mul_C]

theorem word_height (I J : Finset ℤ) :
    BivariateHeight.height (wordOver ℤ I J) ≤
      integerPolynomialHeight (linearOver ℤ I) * integerPolynomialHeight (linearOver ℤ J) := by
  apply bivariate_height_le
  intro y x
  rw [word_coefficient, Int.natAbs_mul]
  exact Nat.mul_le_mul (coeff_natAbs_le_integerPolynomialHeight _ x) (coeff_natAbs_le_integerPolynomialHeight _ y)

theorem word_height_of_bounds (I J : Finset ℤ) (B : ℕ)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ)) :
    BivariateHeight.height (wordOver ℤ I J) ≤ (B + 1) ^ (I.card + J.card) := by
  exact (word_height I J).trans ((Nat.mul_le_mul (linear_height I B hI) (linear_height J B hJ)).trans_eq
    (pow_add (B + 1) I.card J.card).symm)

theorem q_height (I J : Finset ℤ) (B q : ℕ)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hcI : I.card ≤ 2 * q) (hcJ : J.card ≤ 2 * q) :
    BivariateHeight.height (wordOver ℤ I J) ≤ (B + 1) ^ (4 * q) := by
  exact (word_height_of_bounds I J B hI hJ).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

end PaperP1.FormalWordHeight
