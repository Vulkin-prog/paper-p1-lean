module

public import PaperP1.Algebra.HomogeneousPrincipalQuotient
public import PaperP1.Algebra.MvPolynomialHilbert
public import PaperP1.Algebra.GradedHilbertPolynomial
public import PaperP1.Algebra.WeightedPolynomialQuotientGrading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Linarith

/-! # The literal homogeneous plane-equation quotient has Hilbert multiplicity equal to its degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneCurveHilbert

open Polynomial

local instance polynomialRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev CoordinateRing {F : Type*} [Field F] (f : MvPolynomial (Fin 3) F) :=
  MvPolynomial (Fin 3) F ⧸ HomogeneousPrincipalQuotient.ideal f

def piece (F : Type*) [Field F] (f : MvPolynomial (Fin 3) F) (n : ℕ) : Submodule F (CoordinateRing f) :=
  HomogeneousPrincipalQuotient.piece (MvPolynomial.homogeneousSubmodule (Fin 3) F) f n

def polynomial (e : ℕ) : ℚ[X] := C (e : ℚ) * X + C ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)

theorem polynomial_natDegree_le (e : ℕ) : (polynomial e).natDegree ≤ 1 := by
  unfold polynomial
  compute_degree

theorem polynomial_coeff_one (e : ℕ) : (polynomial e).coeff 1 = (e : ℚ) := by simp [polynomial]

theorem polynomial_natDegree (e : ℕ) (he : 0 < e) : (polynomial e).natDegree = 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomial_natDegree_le e)
  rw [polynomial_coeff_one]
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)

theorem polynomial_leadingCoeff (e : ℕ) (he : 0 < e) : (polynomial e).leadingCoeff = (e : ℚ) := by
  rw [Polynomial.leadingCoeff, polynomial_natDegree e he, polynomial_coeff_one]

variable (F : Type*) [Field F] {e : ℕ} (f : MvPolynomial (Fin 3) F)
  (hf : f.IsHomogeneous e) (hf0 : f ≠ 0)

include hf in
theorem ideal_homogeneous : (HomogeneousPrincipalQuotient.ideal f).IsHomogeneous
    (MvPolynomial.homogeneousSubmodule (Fin 3) F) := by
  apply Ideal.homogeneous_span
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact ⟨e, hf⟩

@[instance_reducible] def grading : GradedAlgebra (piece F f) :=
  WeightedPolynomialQuotientGrading.gradedAlgebra (1 : Fin 3 → ℕ)
    (HomogeneousPrincipalQuotient.ideal f) (ideal_homogeneous F f hf)

theorem piece_finite (n : ℕ) : Module.Finite F (piece F f n) := by
  have : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 3) F n) :=
    MvPolynomialHilbert.piece_finite F (Fin 3) n
  exact Module.Finite.of_surjective
    (HomogeneousPrincipalQuotient.quotientMap (MvPolynomial.homogeneousSubmodule (Fin 3) F) f n)
    (HomogeneousPrincipalQuotient.quotientMap_surjective (MvPolynomial.homogeneousSubmodule (Fin 3) F) f n)

include hf hf0 in
theorem piece_finrank_add (n : ℕ) :
    Module.finrank F (piece F f (n + e)) + (n + 2).choose 2 = (n + e + 2).choose 2 := by
  have : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 3) F (n + e)) :=
    MvPolynomialHilbert.piece_finite F (Fin 3) (n + e)
  simpa only [piece, MvPolynomialHilbert.ternary_piece_finrank] using!
    HomogeneousPrincipalQuotient.finrank_add (MvPolynomial.homogeneousSubmodule (Fin 3) F) hf hf0 n

include hf hf0 in
theorem isHilbertPolynomial : GradedHilbertPolynomial.IsHilbertPolynomial (piece F f) (polynomial e) := by
  refine ⟨e, fun n hn ↦ ?_⟩
  have h := congrArg (Nat.cast : ℕ → ℚ) (piece_finrank_add F f hf hf0 (n - e))
  rw [Nat.sub_add_cancel hn] at h
  simp only [Nat.cast_add] at h
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at h
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hn] at h
  simp only [polynomial, eval_add, eval_mul, eval_C, eval_X]
  nlinarith [h]

include hf hf0 in
theorem exists_polynomial : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (piece F f) p :=
  ⟨polynomial e, isHilbertPolynomial F f hf hf0⟩

theorem multiplicity (he : 0 < e) : GradedHilbertPolynomial.multiplicity (piece F f)
    (exists_polynomial F f hf hf0) = (e : ℚ) := by
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ (isHilbertPolynomial F f hf hf0),
    polynomial_natDegree e he, polynomial_leadingCoeff e he]
  simp

end PaperP1.PlaneCurveHilbert
