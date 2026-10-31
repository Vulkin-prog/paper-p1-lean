module

public import PaperP1.Arithmetic.RungeUniform
public import PaperP1.Algebra.IntegerSquareGap
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Companion T1.1: degree-uniform split-product bound

The proof uses the integral Runge truncation, cancellation of its top
coefficients, and separation of integer squares. No analytic tail estimate or
unproved literature bound is assumed.
-/

namespace PaperP1.SplitProductBound

open Finset Polynomial
open scoped BigOperators

theorem square_value_lower_bound
    {k U R : ℕ} (hU : 2 * R ≤ U)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (a : ℤ) (hproduct : (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    U ^ k ≤ 2 ^ k * a.natAbs := by
  have hlocal (i : Fin (2 * k)) : (U : ℤ) ≤ 2 * ((U : ℤ) + γ i) := by
    have hlo := (abs_le.mp (hγ i)).1
    have hUi : 2 * (R : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU
    omega
  have hscaled : (U : ℤ) ^ (2 * k) ≤ (2 : ℤ) ^ (2 * k) * a ^ 2 := by
    calc
      (U : ℤ) ^ (2 * k) = ∏ _i : Fin (2 * k), (U : ℤ) := by simp
      _ ≤ ∏ i : Fin (2 * k), 2 * ((U : ℤ) + γ i) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hlocal i)
      _ = (2 : ℤ) ^ (2 * k) * a ^ 2 := by
        rw [Finset.prod_mul_distrib, hproduct]
        simp
  have hp (z : ℤ) : z ^ (2 * k) = (z ^ k) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp (U : ℤ), hp 2] at hscaled
  have hsquare : ((U : ℤ) ^ k) ^ 2 ≤ ((2 : ℤ) ^ k * |a|) ^ 2 := by
    simpa only [mul_pow, sq_abs] using hscaled
  have hle : (U : ℤ) ^ k ≤ (2 : ℤ) ^ k * |a| :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare
  rw [Int.abs_eq_natAbs] at hle
  exact_mod_cast hle

theorem rungeQ_eval_eq
    {k U : ℕ} (γ : Fin (2 * k) → ℤ) (a : ℤ)
    (hproduct : (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    (RungeQPolynomial.rungeQ γ).eval (U : ℤ) =
      (RungeQPolynomial.rungeScale k * a) ^ 2 -
        ((RungeTruncation.integralRungeTruncation γ).eval (U : ℤ)) ^ 2 := by
  have hG : (RungeQPolynomial.integerSplitProduct γ).eval (U : ℤ) = a ^ 2 := by
    simpa only [RungeQPolynomial.integerSplitProduct, eval_prod, eval_add,
      eval_X, eval_C] using hproduct
  simp only [RungeQPolynomial.rungeQ, eval_sub, eval_mul, eval_C, eval_pow, hG]
  ring

theorem base_le_height_of_nonzero
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R) (hU : 2 * R ≤ U)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (a : ℤ) (hproduct : (∏ i, ((U : ℤ) + γ i)) = a ^ 2)
    (hne : (RungeQPolynomial.rungeQ γ).eval (U : ℤ) ≠ 0) :
    U ≤ integerPolynomialHeight (RungeQPolynomial.rungeQ γ) := by
  have heval := rungeQ_eval_eq γ a hproduct
  have hsqne :
      (RungeQPolynomial.rungeScale k * a) ^ 2 ≠
        ((RungeTruncation.integralRungeTruncation γ).eval (U : ℤ)) ^ 2 := by
    intro h
    exact hne (by rw [heval, h, sub_self])
  have hgap := IntegerSquareGap.natAbs_le_natAbs_sq_sub_sq hsqne
  have hlower := square_value_lower_bound hU γ hγ a hproduct
  have hUpos : 1 ≤ U := by omega
  have hchain :
      2 ^ k * U ^ k ≤
        k * integerPolynomialHeight (RungeQPolynomial.rungeQ γ) * U ^ (k - 1) := by
    calc
      2 ^ k * U ^ k ≤ 2 ^ k * (2 ^ k * a.natAbs) :=
        Nat.mul_le_mul_left _ hlower
      _ = 2 ^ (2 * k) * a.natAbs := by
        rw [← mul_assoc, ← pow_add, show k + k = 2 * k by omega]
      _ ≤ ((RungeQPolynomial.rungeQ γ).eval (U : ℤ)).natAbs := by
        simpa only [heval, RungeQPolynomial.rungeScale, Int.natAbs_mul,
          Int.natAbs_pow, show (2 : ℤ).natAbs = 2 by decide] using hgap
      _ ≤ k * integerPolynomialHeight (RungeQPolynomial.rungeQ γ) * U ^ (k - 1) := by
        simpa only [Nat.sub_add_cancel hk] using
          IntegerSquareGap.eval_natAbs_le (RungeQPolynomial.rungeQ γ)
            (RungeQPolynomial.natDegree_rungeQ_le_pred (by omega) γ) hUpos
  have hfull :
      (2 ^ k * U) * U ^ (k - 1) ≤
        (k * integerPolynomialHeight (RungeQPolynomial.rungeQ γ)) * U ^ (k - 1) := by
    calc
      (2 ^ k * U) * U ^ (k - 1) = 2 ^ k * U ^ k := by
        rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]
      _ ≤ _ := hchain
  have hcan : 2 ^ k * U ≤ k * integerPolynomialHeight (RungeQPolynomial.rungeQ γ) :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < U ^ (k - 1))).mp hfull
  have hkpow : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have hbound : k * U ≤ k * integerPolynomialHeight (RungeQPolynomial.rungeQ γ) :=
    (Nat.mul_le_mul_right U hkpow).trans hcan
  exact (mul_le_mul_iff_right₀ (by omega : 0 < k)).mp hbound

/-- Exact degree-uniform conclusion of technical companion T1.1, with
the even degree represented as `2 * k`. -/
theorem uniform_split_product
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R) (hU : 2 * R ≤ U)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (hinj : Function.Injective γ)
    (a : ℤ) (hproduct : (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    U ≤ (64 * R) ^ (2 * k) := by
  have hheight : U ≤ integerPolynomialHeight (RungeQPolynomial.rungeQ γ) := by
    by_cases heq : (RungeQPolynomial.rungeQ γ).eval (U : ℤ) = 0
    · have hroot := integerRoot_natAbs_le_height
        (RungeQPolynomial.rungeQ_ne_zero (by omega) γ hinj) heq
      simpa using hroot
    · exact base_le_height_of_nonzero hk hR hU γ hγ a hproduct heq
  exact hheight.trans (RungeUniform.rungeQ_height_le hk hR γ hγ)

/-- Manuscript form: the radius may be real and the base is an integer.
Taking the floor of the radius loses no integral shift. -/
theorem uniform_split_product_real_radius
    {k : ℕ} (hk : 1 ≤ k) {R : ℝ} (hR : 1 ≤ R)
    {U : ℤ} (hU : 2 * R ≤ (U : ℝ))
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |(γ i : ℝ)| ≤ R)
    (hinj : Function.Injective γ)
    (a : ℤ) (hproduct : (∏ i, (U + γ i)) = a ^ 2) :
    (U : ℝ) ≤ (64 * R) ^ (2 * k) := by
  have hR0 : 0 ≤ R := by linarith
  have hRfloor : 1 ≤ ⌊R⌋₊ := (Nat.one_le_floor_iff R).mpr hR
  have hfloor : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
  have hU0 : 0 ≤ U := by
    have hUr : (0 : ℝ) ≤ U := by linarith
    exact_mod_cast hUr
  have hUnat : (U.toNat : ℤ) = U := Int.toNat_of_nonneg hU0
  have hUreal : (U.toNat : ℝ) = (U : ℝ) := by exact_mod_cast hUnat
  have hUfloor : 2 * ⌊R⌋₊ ≤ U.toNat := by
    have hle : (2 : ℝ) * ⌊R⌋₊ ≤ U.toNat := by rw [hUreal]; linarith
    exact_mod_cast hle
  have hγfloor : ∀ i, |γ i| ≤ (⌊R⌋₊ : ℤ) := by
    intro i
    have hcast : (γ i).natAbs ≤ ⌊R⌋₊ := Nat.le_floor (by simpa using hγ i)
    simpa only [Int.abs_eq_natAbs, Nat.cast_le] using hcast
  have hproduct' : (∏ i, ((U.toNat : ℤ) + γ i)) = a ^ 2 := by
    simpa only [hUnat] using hproduct
  have hbound := uniform_split_product hk hRfloor hUfloor γ hγfloor hinj a hproduct'
  have hboundReal : (U.toNat : ℝ) ≤ (64 * (⌊R⌋₊ : ℝ)) ^ (2 * k) := by
    exact_mod_cast hbound
  rw [hUreal] at hboundReal
  exact hboundReal.trans
    (pow_le_pow_left₀ (by positivity) (by linarith) (2 * k))

end PaperP1.SplitProductBound

