module

public import PaperP1.Algebra.RectangularPolynomialCoordinates
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Actual curve multiples give a fixed fractional gap in the evaluation rank

The enlarged rectangular coefficient space retains every bounded-degree
multiple of the original nonzero equation. No rank estimate is an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialMultipleEvaluationRank

open Polynomial Finset Submodule RectangularPolynomialCoordinates

theorem inner_product_degree_le (D : ℕ) (F P : ℚ[X][X])
    (hF : ∀ y, (F.coeff y).natDegree ≤ D) (hP : ∀ y, (P.coeff y).natDegree ≤ D) (y : ℕ) :
    ((F * P).coeff y).natDegree ≤ 2 * D := by
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact Polynomial.natDegree_mul_le.trans (by have hf := hF i.1; have hp := hP i.2; omega)

def multiplyCoordinates (D : ℕ) (F : ℚ[X][X]) : (Index D → ℚ) →ₗ[ℚ] (Index (2 * D) → ℚ) :=
  (coefficientsLinear (2 * D)).comp ((LinearMap.mulLeft ℚ F).comp (polynomialLinear D))

theorem multiply_reconstruction (D : ℕ) (F : ℚ[X][X])
    (houter : F.natDegree ≤ D) (hinner : ∀ y, (F.coeff y).natDegree ≤ D) (w : Index D → ℚ) :
    polynomial (2 * D) (multiplyCoordinates D F w) = F * polynomial D w := by
  change polynomial (2 * D) (coefficientsLinear (2 * D) (F * polynomial D w)) = F * polynomial D w
  apply reconstruction
  · exact Polynomial.natDegree_mul_le.trans (by have hh := outer_degree_le D w; omega)
  · exact inner_product_degree_le D F (polynomial D w) hinner (inner_degree_le D w)

theorem multiply_injective (D : ℕ) (F : ℚ[X][X]) (hF : F ≠ 0)
    (houter : F.natDegree ≤ D) (hinner : ∀ y, (F.coeff y).natDegree ≤ D) :
    Function.Injective (multiplyCoordinates D F) := by
  intro u v h
  have hh := congrArg (polynomial (2 * D)) h
  rw [multiply_reconstruction D F houter hinner, multiply_reconstruction D F houter hinner] at hh
  exact polynomial_injective D (mul_left_cancel₀ hF hh)

def evaluationMatrix (D : ℕ) (S : Finset (ℤ × ℤ)) : Matrix S (Index D) ℚ :=
  fun z i ↦ (z.val.1 : ℚ) ^ i.1.val * (z.val.2 : ℚ) ^ i.2.val

def evaluationLinear (D : ℕ) (S : Finset (ℤ × ℤ)) : (Index D → ℚ) →ₗ[ℚ] (S → ℚ) :=
  (evaluationMatrix D S).mulVecLin

theorem evaluation_apply (D : ℕ) (S : Finset (ℤ × ℤ)) (w : Index D → ℚ) (z : S) :
    evaluationLinear D S w z = (polynomial D w).evalEval (z.val.1 : ℚ) (z.val.2 : ℚ) := by
  change (∑ i : Index D, ((z.val.1 : ℚ) ^ i.1.val * (z.val.2 : ℚ) ^ i.2.val) * w i) = _
  rw [evaluation]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem multiples_in_kernel (D : ℕ) (F : ℚ[X][X])
    (houter : F.natDegree ≤ D) (hinner : ∀ y, (F.coeff y).natDegree ≤ D)
    (S : Finset (ℤ × ℤ)) (hzero : ∀ z ∈ S, F.evalEval (z.1 : ℚ) (z.2 : ℚ) = 0) :
    LinearMap.range (multiplyCoordinates D F) ≤ LinearMap.ker (evaluationLinear (2 * D) S) := by
  rintro _ ⟨w, rfl⟩
  apply LinearMap.mem_ker.mpr
  funext z
  change evaluationLinear (2 * D) S (multiplyCoordinates D F w) z = 0
  rw [evaluation_apply, multiply_reconstruction D F houter hinner, Polynomial.evalEval_mul,
    hzero z.val z.property, zero_mul]

theorem fractional_rank_gap (D : ℕ) (F : ℚ[X][X]) (hF : F ≠ 0)
    (houter : F.natDegree ≤ D) (hinner : ∀ y, (F.coeff y).natDegree ≤ D)
    (S : Finset (ℤ × ℤ)) (hzero : ∀ z ∈ S, F.evalEval (z.1 : ℚ) (z.2 : ℚ) = 0) :
    8 * Module.finrank ℚ (span ℚ (Set.range (evaluationMatrix (2 * D) S).row)) ≤
      7 * Fintype.card (Index (2 * D)) := by
  classical
  have hi := multiply_injective D F hF houter hinner
  have hm := (multiplyCoordinates D F).finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr hi, finrank_bot, add_zero] at hm
  have hmul : Module.finrank ℚ (LinearMap.range (multiplyCoordinates D F)) = (D + 1) ^ 2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, pow_two] using hm
  have hk := Submodule.finrank_mono (multiples_in_kernel D F houter hinner S hzero)
  rw [hmul] at hk
  have he := (evaluationLinear (2 * D) S).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℚ (Index (2 * D) → ℚ) = (2 * D + 1) ^ 2 := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, pow_two]
  rw [hdim] at he
  have hsize : (2 * D + 1) ^ 2 ≤ 8 * (D + 1) ^ 2 := by nlinarith only [Nat.zero_le D, Nat.zero_le (D ^ 2)]
  rw [← Matrix.rank_eq_finrank_span_row]
  change 8 * Module.finrank ℚ (LinearMap.range (evaluationLinear (2 * D) S)) ≤
    7 * Fintype.card (Index (2 * D))
  simp only [Fintype.card_prod, Fintype.card_fin]
  nlinarith only [hk, he, hsize]

end PaperP1.PolynomialMultipleEvaluationRank
