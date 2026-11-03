module

public import PaperP1.Algebra.PlaneCurveHilbert
public import PaperP1.Algebra.GradedVeroneseHilbertPolynomial

/-! # The actual D-th Veronese of a plane equation has Hilbert degree De -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneCurveVeroneseHilbert

variable (F : Type*) [Field F] {e : ℕ} (f : MvPolynomial (Fin 3) F)
  (hf : f.IsHomogeneous e)

abbrev CoordinateRing (D : ℕ) :=
  letI := PlaneCurveHilbert.grading F f hf
  GradedVeroneseAlgebra.veronese (PlaneCurveHilbert.piece F f) D

def piece (D n : ℕ) : Submodule F (CoordinateRing F f hf D) := by
  letI := PlaneCurveHilbert.grading F f hf
  exact GradedVeroneseGrading.piece (PlaneCurveHilbert.piece F f) D n

@[instance_reducible] def grading (D : ℕ) (hD : 0 < D) : GradedAlgebra (piece F f hf D) := by
  letI := PlaneCurveHilbert.grading F f hf
  exact GradedVeroneseGrading.grading (PlaneCurveHilbert.piece F f) D hD

theorem piece_finrank (D n : ℕ) : Module.finrank F (piece F f hf D n) =
    Module.finrank F (PlaneCurveHilbert.piece F f (n * D)) := by
  let := PlaneCurveHilbert.grading F f hf
  exact GradedVeronesePieceEquiv.finrank_eq (PlaneCurveHilbert.piece F f) D n

theorem piece_finite (D n : ℕ) : Module.Finite F (piece F f hf D n) := by
  let := PlaneCurveHilbert.grading F f hf
  have := PlaneCurveHilbert.piece_finite F f (n * D)
  exact GradedVeronesePieceEquiv.finite (PlaneCurveHilbert.piece F f) D n

variable (hf0 : f ≠ 0) (D : ℕ) (hD : 0 < D)

include hf0 hD in
theorem isHilbertPolynomial : GradedHilbertPolynomial.IsHilbertPolynomial (piece F f hf D)
    (GradedVeroneseHilbertPolynomial.rescale D (PlaneCurveHilbert.polynomial e)) := by
  let := PlaneCurveHilbert.grading F f hf
  exact GradedVeroneseHilbertPolynomial.isHilbertPolynomial (PlaneCurveHilbert.piece F f) D
    (PlaneCurveHilbert.isHilbertPolynomial F f hf hf0) hD

include hf0 hD in
theorem exists_polynomial : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (piece F f hf D) p :=
  ⟨_, isHilbertPolynomial F f hf hf0 D hD⟩

include hD in
theorem polynomial_natDegree (he : 0 < e) :
    (GradedVeroneseHilbertPolynomial.rescale D (PlaneCurveHilbert.polynomial e)).natDegree = 1 := by
  rw [GradedVeroneseHilbertPolynomial.rescale_natDegree D _ hD, PlaneCurveHilbert.polynomial_natDegree e he]

include hD in
theorem polynomial_leadingCoeff (he : 0 < e) :
    (GradedVeroneseHilbertPolynomial.rescale D (PlaneCurveHilbert.polynomial e)).leadingCoeff =
      ((D * e : ℕ) : ℚ) := by
  rw [GradedVeroneseHilbertPolynomial.rescale_leadingCoeff D _ hD,
    PlaneCurveHilbert.polynomial_natDegree e he, PlaneCurveHilbert.polynomial_leadingCoeff e he,
    pow_one, Nat.cast_mul, mul_comm]

theorem multiplicity (he : 0 < e) : GradedHilbertPolynomial.multiplicity (piece F f hf D)
    (exists_polynomial F f hf hf0 D hD) = ((D * e : ℕ) : ℚ) := by
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ (isHilbertPolynomial F f hf hf0 D hD),
    polynomial_natDegree D hD he, polynomial_leadingCoeff D hD he]
  simp

end PaperP1.PlaneCurveVeroneseHilbert
