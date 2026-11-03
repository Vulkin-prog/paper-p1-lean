module

public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Probability.PoissonFactorialMoments
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Exact ordinary moments, the actual Poisson Touchard polynomial and its quadratic derivative correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TouchardCountMoments

open Finset Polynomial PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.FactorialCountMoments PaperP1.Algebra PaperP1.Probability

def touchard (r : ℕ) : ℝ[X] :=
  ∑ j ∈ range (r + 1), C (Nat.stirlingSecond r j : ℝ) * X ^ j

theorem eval_touchard (r : ℕ) (u : ℝ) :
    (touchard r).eval u = ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * u ^ j := by
  simp only [touchard, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem ordinary_eq_factorial {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    countMoment G L r = ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * factorialCountMoment G L j := by
  rw [countMoment_eq_finite hG]
  have hid (n : ℕ) : (n : ℝ) ^ r =
      ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * (n.descFactorial j : ℝ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n r
  simp_rw [hid]
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro j _hj
  rw [finiteExpectation_const_mul, ← factorialCountMoment_eq_finite hG j]

theorem poisson_hasSum (r : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    HasSum (fun k : ℕ ↦ PoissonSequence.mass u k * (k : ℝ) ^ r) ((touchard r).eval u) := by
  have hper (j : ℕ) (_hj : j ∈ range (r + 1)) :=
    (PoissonFactorialMoments.hasSum_mass_factorial u hu j).mul_left (Nat.stirlingSecond r j : ℝ)
  have h := hasSum_sum hper
  rw [eval_touchard]
  convert h using 1
  funext k
  have hid : (k : ℝ) ^ r =
      ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * (k.descFactorial j : ℝ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k r
  rw [hid, mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

theorem second_derivative (r : ℕ) (u : ℝ) :
    ((touchard r).derivative.derivative).eval u / 2 =
      ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ) * (j.choose 2 : ℝ) * u ^ (j - 2) := by
  have heq : (touchard r).derivative.derivative =
      ∑ j ∈ range (r + 1), C ((Nat.stirlingSecond r j : ℝ) * (j.descFactorial 2 : ℝ)) * X ^ (j - 2) := by
    change (Polynomial.derivative^[2]) (touchard r) = _
    rw [touchard, iterate_derivative_sum]
    apply sum_congr rfl
    intro j _hj
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul]
  rw [heq, eval_finsetSum, sum_div]
  apply sum_congr rfl
  intro j _hj
  simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, Nat.factorial, Nat.cast_one, mul_one]
  ring

theorem count_zero {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) : countMoment G L 0 = 1 := by
  rw [ordinary_eq_factorial hG 0]
  simp only [Nat.zero_add, range_one, sum_singleton, Nat.stirlingSecond_zero, Nat.cast_one, one_mul]
  rw [factorialCountMoment_eq_subset hG 0]
  simp only [Nat.factorial_zero, Nat.cast_one, powersetCard_zero, sum_singleton, infiniteJointMoment_empty, mul_one]

end PaperP1.TouchardCountMoments
