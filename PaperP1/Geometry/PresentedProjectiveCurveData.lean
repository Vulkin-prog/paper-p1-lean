module

public import PaperP1.Geometry.GradedProjectiveCurveData
public import PaperP1.Algebra.GradedSurjectivePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # A presented projective curve has the same actual polynomial-coordinate ideal and genuine Hilbert degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PresentedProjectiveCurveData

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ B : Type} [CommRing B] [Algebra ℚ B]
  {H : ℕ → Submodule ℚ B} [GradedAlgebra H]
  (f : MvPolynomial.homogeneousSubmodule σ ℚ →+*ᵍ H)
  (hscalar : ∀ a : ℚ, f (algebraMap ℚ (MvPolynomial σ ℚ) a) = algebraMap ℚ B a)
  (honto : Function.Surjective f) (Γ : GradedProjectiveCurveData.Curve H)

def coordinateIdeal : Ideal (MvPolynomial σ ℚ) := Γ.ideal.comap f.toRingHom

def evaluation : MvPolynomial.homogeneousSubmodule σ ℚ →+*ᵍ
    HomogeneousQuotientGrading.piece H Γ.ideal := (HomogeneousQuotientGrading.mk H Γ.ideal).comp f

theorem kernel_eq : RingHom.ker (evaluation f Γ).toRingHom = coordinateIdeal f Γ := by
  change RingHom.ker ((Ideal.Quotient.mk Γ.ideal).comp f.toRingHom) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  rfl

include honto in
theorem evaluation_surjective : Function.Surjective (evaluation f Γ) := Ideal.Quotient.mk_surjective.comp honto

include hscalar in
theorem evaluation_commutes (a : ℚ) : evaluation f Γ (algebraMap ℚ (MvPolynomial σ ℚ) a) =
    algebraMap ℚ (B ⧸ Γ.ideal) a := by
  change Ideal.Quotient.mk Γ.ideal (f (algebraMap ℚ (MvPolynomial σ ℚ) a)) = _
  rw [hscalar]
  rfl

theorem coordinateIdeal_prime : (coordinateIdeal f Γ).IsPrime := by
  let : Γ.ideal.IsPrime := Γ.ideal_prime
  exact Ideal.IsPrime.comap f.toRingHom

theorem coordinateIdeal_homogeneous : (coordinateIdeal f Γ).IsHomogeneous
    (MvPolynomial.homogeneousSubmodule σ ℚ) :=
  (HomogeneousIdeal.comap f Γ.point.asHomogeneousIdeal).isHomogeneous

include hscalar honto in
theorem piece_finrank (n : ℕ) :
    Module.finrank ℚ (ProjectiveCurveData.piece (coordinateIdeal f Γ) n) =
      Module.finrank ℚ (HomogeneousQuotientGrading.piece H Γ.ideal n) := by
  let := HomogeneousQuotientGrading.grading H Γ.ideal Γ.ideal_homogeneous
  have hh := GradedSurjectivePresentation.piece_finrank (evaluation f Γ)
    (evaluation_commutes f hscalar Γ) (evaluation_surjective f honto Γ) n
  change Module.finrank ℚ (HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule σ ℚ)
    (RingHom.ker (evaluation f Γ).toRingHom) n) = _ at hh
  rw [kernel_eq] at hh
  exact hh

include hscalar honto in
theorem coordinate_hilbert : GradedHilbertPolynomial.IsHilbertPolynomial
    (ProjectiveCurveData.piece (coordinateIdeal f Γ))
    (Polynomial.C Γ.degree * Polynomial.X + Polynomial.C Γ.constant) := by
  obtain ⟨N, hN⟩ := Γ.hilbert
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [piece_finrank f hscalar honto Γ n]
  exact hN n hn

def toCurve : ProjectiveCurveData.Curve σ where
  ideal := coordinateIdeal f Γ
  prime := coordinateIdeal_prime f Γ
  homogeneous := coordinateIdeal_homogeneous f Γ
  degree := Γ.degree
  degree_pos := Γ.degree_pos
  constant := Γ.constant
  hilbert := coordinate_hilbert f hscalar honto Γ

theorem toCurve_ideal : (toCurve f hscalar honto Γ).ideal = coordinateIdeal f Γ := rfl

theorem toCurve_degree : (toCurve f hscalar honto Γ).degree = Γ.degree := rfl

end PaperP1.PresentedProjectiveCurveData
