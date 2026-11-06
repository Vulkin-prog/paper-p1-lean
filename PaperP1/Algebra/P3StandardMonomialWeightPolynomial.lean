module

public import PaperP1.Algebra.P3StandardMonomialWeightBudget
public import PaperP1.Algebra.ProjectiveHypersurfaceHilbert
public import Mathlib.Tactic.ComputeDegree

/-! # The exact genuine quadratic size and cubic height-weight polynomials of standard surface monomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardMonomialWeightPolynomial

open Polynomial P3StandardMonomialCount NormalizedP3MonomialHeight
open scoped Classical

def polynomial (d : ℕ) : ℚ[X] :=
  C ((d : ℚ) / 3) * X ^ 3 + C ((5 * (d : ℚ) - (d : ℚ) ^ 2) / 4) * X ^ 2 +
    C ((11 * (d : ℚ) - 3 * (d : ℚ) ^ 2) / 12) * X +
      C (((d : ℚ) ^ 4 - 6 * (d : ℚ) ^ 3 + 11 * (d : ℚ) ^ 2 - 6 * (d : ℚ)) / 24)

theorem cardinality_polynomial (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) :
    (Fintype.card (StandardIndex μ e) : ℚ) =
      (ProjectiveHypersurfaceHilbert.polynomial μ.degree).eval (e : ℚ) := by
  have hc := congrArg (Nat.cast : ℕ → ℚ) (P3StandardMonomialWeightBudget.cardinality_add μ e he)
  simp only [Nat.cast_add] at hc
  rw [QuaternaryPolynomialHilbert.cast_choose_three (e - μ.degree),
    QuaternaryPolynomialHilbert.cast_choose_three e] at hc
  simp only [Nat.cast_sub he] at hc
  simp only [ProjectiveHypersurfaceHilbert.polynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  nlinarith only [hc]

theorem weight_sum_polynomial (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) (hμ : μ 3 = 0) :
    ((∑ r : StandardIndex μ e, freeDegree r.val.val : ℕ) : ℚ) = (polynomial μ.degree).eval (e : ℚ) := by
  have hs := congrArg (Nat.cast : ℕ → ℚ) (P3StandardMonomialWeightBudget.scaled_free_budget μ e he hμ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs
  rw [QuaternaryPolynomialHilbert.cast_choose_three (e - μ.degree),
    QuaternaryPolynomialHilbert.cast_choose_three e] at hs
  simp only [Nat.cast_sub he] at hs
  simp only [polynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  nlinarith only [hs]

theorem natDegree_le (d : ℕ) : (polynomial d).natDegree ≤ 3 := by unfold polynomial; compute_degree

theorem coeff_three (d : ℕ) : (polynomial d).coeff 3 = (d : ℚ) / 3 := by simp [polynomial]

end PaperP1.P3StandardMonomialWeightPolynomial
