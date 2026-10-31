module

public import PaperP1.Algebra.RungeQPolynomial

@[expose] public section

/-!
# Degree-uniform Runge estimates

New estimates for companion T1.1. The scaled truncation and its cancellation
come from the explicitly recorded Paper C ports. These bounds retain the
coefficient's degree weight instead of squaring a global polynomial height.
-/

namespace PaperP1.RungeUniform

open Finset Polynomial
open scoped BigOperators

theorem coeff_integralRungeTruncation_of_le
    {k n : ℕ} (γ : Fin (2 * k) → ℤ) (hn : n ≤ k) :
    (RungeTruncation.integralRungeTruncation γ).coeff n =
      RungeTruncation.scaledRungeCoefficientUpTo γ (k - n) := by
  classical
  rw [RungeTruncation.integralRungeTruncation, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (k - n)]
  · simp [Nat.sub_sub_self hn]
  · intro b hb hbn
    have hb' : b ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hb
    have hne : k - b ≠ n := by omega
    simp [Polynomial.coeff_monomial, hne]
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (by omega)))

theorem scaledRungeCoefficient_natAbs_le_weighted
    {k m R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (hm : m ≤ k) :
    (RungeTruncation.scaledRungeCoefficientUpTo γ m).natAbs ≤
      2 ^ (4 * k + m) * R ^ m := by
  have hγq : ∀ i, |(γ i : ℚ)| ≤ (R : ℚ) := by
    intro i
    exact_mod_cast hγ i
  have hc := RungeCoefficients.abs_rungeCoefficient_le
    (by omega : 0 < 2 * k) (by positivity : (0 : ℚ) ≤ R) hγq (m := m)
  have hscaled := RungeTruncation.scaledRungeCoefficientUpTo_spec γ hm
  have hcast :
      ((RungeTruncation.scaledRungeCoefficientUpTo γ m).natAbs : ℚ) ≤
        ((2 ^ (4 * k + m) * R ^ m : ℕ) : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, hscaled, abs_mul, abs_pow]
    norm_num only [abs_of_nonneg (show (0 : ℚ) ≤ 2 by norm_num)]
    calc
      (2 : ℚ) ^ (2 * k) * |RungeCoefficients.rungeCoefficient γ m| ≤
          (2 : ℚ) ^ (2 * k) * ((2 : ℚ) ^ (m + 2 * k) * (R : ℚ) ^ m) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = ((2 ^ (4 * k + m) * R ^ m : ℕ) : ℚ) := by
        push_cast
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
  exact_mod_cast hcast

theorem truncation_coeff_product_natAbs_le
    {k a b R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (ha : a ≤ k) (hb : b ≤ k) :
    ((RungeTruncation.integralRungeTruncation γ).coeff a *
      (RungeTruncation.integralRungeTruncation γ).coeff b).natAbs ≤
        2 ^ (10 * k) * R ^ (2 * k) := by
  rw [Int.natAbs_mul, coeff_integralRungeTruncation_of_le γ ha,
    coeff_integralRungeTruncation_of_le γ hb]
  calc
    _ ≤ (2 ^ (4 * k + (k - a)) * R ^ (k - a)) *
        (2 ^ (4 * k + (k - b)) * R ^ (k - b)) :=
      Nat.mul_le_mul
        (scaledRungeCoefficient_natAbs_le_weighted hk hR γ hγ (by omega))
        (scaledRungeCoefficient_natAbs_le_weighted hk hR γ hγ (by omega))
    _ = 2 ^ ((4 * k + (k - a)) + (4 * k + (k - b))) *
        R ^ ((k - a) + (k - b)) := by
      rw [pow_add, pow_add]
      ring
    _ ≤ 2 ^ (10 * k) * R ^ (2 * k) :=
      Nat.mul_le_mul
        (Nat.pow_le_pow_right (by norm_num) (by omega))
        (Nat.pow_le_pow_right hR (by omega))

theorem truncation_sq_coeff_natAbs_le
    {k n R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (hn : n < k) :
    (((RungeTruncation.integralRungeTruncation γ) ^ 2).coeff n).natAbs ≤
      k * (2 ^ (10 * k) * R ^ (2 * k)) := by
  rw [pow_two, Polynomial.coeff_mul]
  calc
    _ ≤ ∑ ab ∈ antidiagonal n,
        ((RungeTruncation.integralRungeTruncation γ).coeff ab.1 *
          (RungeTruncation.integralRungeTruncation γ).coeff ab.2).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _ab ∈ antidiagonal n, 2 ^ (10 * k) * R ^ (2 * k) := by
      apply sum_le_sum
      intro ab hab
      have hab' : ab.1 + ab.2 = n := mem_antidiagonal.mp hab
      exact truncation_coeff_product_natAbs_le hk hR γ hγ (by omega) (by omega)
    _ = (n + 1) * (2 ^ (10 * k) * R ^ (2 * k)) := by simp
    _ ≤ k * (2 ^ (10 * k) * R ^ (2 * k)) :=
      Nat.mul_le_mul_right _ (by omega)

theorem rungeQ_coeff_natAbs_le_weighted
    {k n R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    ((RungeQPolynomial.rungeQ γ).coeff n).natAbs ≤
      (k + 1) * (2 ^ (10 * k) * R ^ (2 * k)) := by
  by_cases hn : n < k
  · rw [RungeQPolynomial.coeff_rungeQ]
    calc
      _ ≤ (RungeQPolynomial.rungeScale k ^ 2 *
          (RungeQPolynomial.integerSplitProduct γ).coeff n).natAbs +
          (((RungeTruncation.integralRungeTruncation γ) ^ 2).coeff n).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 ^ (10 * k) * R ^ (2 * k) +
          k * (2 ^ (10 * k) * R ^ (2 * k)) := by
        apply Nat.add_le_add
        · rw [Int.natAbs_mul, Int.natAbs_pow, RungeQPolynomial.rungeScale]
          norm_num only [Int.natAbs_pow, Int.natAbs_natCast]
          calc
            _ ≤ (2 ^ (2 * k)) ^ 2 * (2 ^ (2 * k) * R ^ (2 * k)) :=
              Nat.mul_le_mul_left _ (RungeQPolynomial.coeff_integerSplitProduct_natAbs_le (by omega) hR γ hγ)
            _ = 2 ^ (6 * k) * R ^ (2 * k) := by
              rw [← pow_mul, ← mul_assoc, ← pow_add]
              congr 2
              omega
            _ ≤ 2 ^ (10 * k) * R ^ (2 * k) :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        · exact truncation_sq_coeff_natAbs_le hk hR γ hγ hn
      _ = (k + 1) * (2 ^ (10 * k) * R ^ (2 * k)) := by ring
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (RungeQPolynomial.natDegree_rungeQ_le_pred (by omega) γ) (by omega))]
    simp

theorem rungeQ_height_le
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ) (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    integerPolynomialHeight (RungeQPolynomial.rungeQ γ) ≤
      (64 * R) ^ (2 * k) := by
  have hcount : k + 1 ≤ 2 ^ (2 * k) := by
    have hsmall : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt Nat.lt_two_pow_self
    have hp : 2 ^ k ≤ 2 ^ (2 * k) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hsmall.trans hp
  unfold integerPolynomialHeight
  apply Finset.sup_le
  intro n _
  calc
    _ ≤ (k + 1) * (2 ^ (10 * k) * R ^ (2 * k)) :=
      rungeQ_coeff_natAbs_le_weighted hk hR γ hγ
    _ ≤ 2 ^ (2 * k) * (2 ^ (10 * k) * R ^ (2 * k)) :=
      Nat.mul_le_mul_right _ hcount
    _ = (64 * R) ^ (2 * k) := by
      rw [← mul_assoc, ← pow_add, mul_pow]
      congr 1
      calc
        2 ^ (2 * k + 10 * k) = (2 ^ 6) ^ (2 * k) := by
          rw [← pow_mul]
          congr 1
          omega
        _ = 64 ^ (2 * k) := by norm_num

end PaperP1.RungeUniform

