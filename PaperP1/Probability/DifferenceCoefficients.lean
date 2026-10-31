module

public import PaperP1.Probability.FactorialGeneratingPolynomial
public import PaperP1.Probability.FiniteLawEmbedding
public import Mathlib.Data.Nat.Choose.Sum

/-! # Exact coefficients and norm of every finite forward difference

The finite convolution ring is identified with ordinary polynomials only
through Mathlib's coefficient-preserving ring equivalence. No numerical
coefficient pattern or norm equality is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DifferenceCoefficients

open PaperP1.Probability PaperP1.FactorialGeneratingPolynomial PaperP1.FiniteLawEmbedding
  Polynomial Finset

def ordinaryEquiv : SignedLaw ℝ ≃+* ℝ[X] := (Polynomial.toFinsuppIso ℝ).symm

theorem ordinaryEquiv_coeff (ν : SignedLaw ℝ) (k : ℕ) :
    (ordinaryEquiv ν).coeff k = ν.coeff k := rfl

theorem ordinaryEquiv_atom (n : ℕ) : ordinaryEquiv (atom n) = X ^ n := by
  ext k
  rw [ordinaryEquiv_coeff]
  simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Polynomial.coeff_X_pow]
  simp only [eq_comm]

theorem ordinaryEquiv_forwardDifference : ordinaryEquiv forwardDifference = X - 1 := by
  rw [forwardDifference, map_sub, ordinaryEquiv_atom, ordinaryEquiv_atom, pow_one, pow_zero]

theorem forwardDifference_pow_coeff (m k : ℕ) :
    ((forwardDifference : SignedLaw ℝ) ^ m).coeff k = (-1 : ℝ) ^ (m - k) * (m.choose k : ℝ) := by
  rw [← ordinaryEquiv_coeff, map_pow, ordinaryEquiv_forwardDifference]
  have heq : (X - 1 : ℝ[X]) = X + C (-1) := by simp only [map_neg, C_1, sub_eq_add_neg]
  rw [heq, Polynomial.coeff_X_add_C_pow]

theorem abs_forwardDifference_pow_coeff (m k : ℕ) :
    |((forwardDifference : SignedLaw ℝ) ^ m).coeff k| = (m.choose k : ℝ) := by
  rw [forwardDifference_pow_coeff, abs_mul, abs_pow]
  norm_num

theorem support_forwardDifference_pow (m : ℕ) :
    ((forwardDifference : SignedLaw ℝ) ^ m).coeff.support ⊆ range (m + 1) := by
  intro k hk
  apply mem_range.mpr
  by_contra hn
  have hmk : m < k := by omega
  have hz : ((forwardDifference : SignedLaw ℝ) ^ m).coeff k = 0 := by
    rw [forwardDifference_pow_coeff, Nat.choose_eq_zero_of_lt hmk, Nat.cast_zero, mul_zero]
  exact Finsupp.mem_support_iff.mp hk hz

theorem l1Norm_forwardDifference_pow (m : ℕ) :
    l1Norm ((forwardDifference : SignedLaw ℝ) ^ m) = (2 : ℝ) ^ m := by
  rw [l1Norm_eq_sum_of_support_subset _ _ (support_forwardDifference_pow m)]
  simp_rw [abs_forwardDifference_pow_coeff]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

theorem abs_coeff_mul_factorial_le (m k : ℕ) :
    |((forwardDifference : SignedLaw ℝ) ^ m).coeff k| * (k.factorial : ℝ) ≤ (m.factorial : ℝ) := by
  rw [abs_forwardDifference_pow_coeff]
  by_cases hk : k ≤ m
  · have h := Nat.choose_mul_factorial_mul_factorial hk
    have hm : 1 ≤ (m - k).factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hle : m.choose k * k.factorial ≤ m.factorial := by nlinarith
    exact_mod_cast hle
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk), Nat.cast_zero, zero_mul]
    exact Nat.cast_nonneg _

theorem finite_factorial_moment (ν : SignedLaw ℝ) (j : ℕ) :
    (∑ k ∈ ν.coeff.support, ν.coeff k * (k.descFactorial j : ℝ)) =
      (j.factorial : ℝ) * (transform ν).coeff j := by
  rw [transform_eq_sum]
  unfold Finsupp.sum
  rw [Polynomial.finsetSum_coeff, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem difference_factorial_moment (m j : ℕ) :
    (∑ k ∈ ((forwardDifference : SignedLaw ℝ) ^ m).coeff.support,
      ((forwardDifference : SignedLaw ℝ) ^ m).coeff k * (k.descFactorial j : ℝ)) =
        if m = j then (m.factorial : ℝ) else 0 := by
  rw [finite_factorial_moment, map_pow, transform_forwardDifference, Polynomial.coeff_X_pow]
  by_cases h : m = j
  · subst j
    simp
  · simp [h, Ne.symm h]

theorem hasSum_weighted_finite (ν : SignedLaw ℝ) (f : ℕ → ℝ) :
    HasSum (fun k ↦ ν.coeff k * f k) (∑ k ∈ ν.coeff.support, ν.coeff k * f k) := by
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  rw [Finsupp.notMem_support_iff.mp hk, zero_mul]

end PaperP1.DifferenceCoefficients
