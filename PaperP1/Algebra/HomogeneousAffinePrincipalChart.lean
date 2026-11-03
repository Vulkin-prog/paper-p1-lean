module

public import PaperP1.Algebra.NativeAffineChart
public import PaperP1.Algebra.PlaneCurveHilbert
public import PaperP1.Algebra.GradedQuotientChartMap
public import PaperP1.Algebra.GradedDehomogenizationPieces
public import PaperP1.Algebra.AffineCurveFunctionField
public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Geometry.ProjIntegral

/-! # The actual affine equation of a homogeneous irreducible plane curve remains irreducible on its nonempty Z-chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousAffinePrincipalChart

open Polynomial HomogeneousLocalization MvPolynomial PaperP1.HomogeneousPrincipalQuotient

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type*} [Field F]

local instance nativeRing : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance affineRing : CommRing F[X][X] := inferInstance

abbrev CoordinateRing (f : MvPolynomial (Fin 3) F) := MvPolynomial (Fin 3) F ⧸ ideal f

local instance coordinateRing (f : MvPolynomial (Fin 3) F) : CommRing (CoordinateRing f) := inferInstance
local instance affineCoordinateRing (f : MvPolynomial (Fin 3) F) :
    CommRing (AffineCurveFunctionField.CoordinateRing (NativeAffineChart.specialization F f)) := inferInstance

local instance idealPrime (f : MvPolynomial (Fin 3) F) [h : Fact (Irreducible f)] : (ideal f).IsPrime :=
  (Ideal.span_singleton_prime h.out.ne_zero).mpr h.out.prime

def piece (f : MvPolynomial (Fin 3) F) (n : ℕ) : Submodule F (CoordinateRing f) :=
  HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 3) F) (ideal f) n

@[instance_reducible] def grading (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e) :
    GradedAlgebra (piece f) :=
  HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3) F) (ideal f)
    (PlaneCurveHilbert.ideal_homogeneous F f hf)

def chartCoordinate (f : MvPolynomial (Fin 3) F) : CoordinateRing f := Ideal.Quotient.mk (ideal f) (X (2 : Fin 3))

theorem chartCoordinate_mem (f : MvPolynomial (Fin 3) F) : chartCoordinate f ∈ piece f 1 :=
  Submodule.mem_map.mpr ⟨X (2 : Fin 3), isHomogeneous_X F 2, rfl⟩

theorem chartCoordinate_ne_zero (f : MvPolynomial (Fin 3) F) (hZ : X (2 : Fin 3) ∉ ideal f) :
    chartCoordinate f ≠ 0 := fun hz ↦ hZ (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem chartIdeal_eq (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e) :
    letI := grading f hf
    (RingHom.ker (HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin 3) F) (ideal f)).toRingHom).map
      ((NativeAffineChart.originalEquiv F).toRingHom.comp
        (GradedDehomogenization.map (homogeneousSubmodule (Fin 3) F) (isHomogeneous_X F (2 : Fin 3)))) =
      AffineCurveFunctionField.ideal (NativeAffineChart.specialization F f) := by
  let := grading f hf
  have heq : (NativeAffineChart.originalEquiv F).toRingHom.comp
      (GradedDehomogenization.map (homogeneousSubmodule (Fin 3) F) (isHomogeneous_X F (2 : Fin 3))) =
        NativeAffineChart.specialization F := by
    apply RingHom.ext
    intro p
    exact NativeAffineChart.originalEquiv_dehomogenization F p
  have hk : RingHom.ker (HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin 3) F) (ideal f)).toRingHom =
      ideal f := Ideal.mk_ker
  rw [hk, heq, ideal, Ideal.map_span, Set.image_singleton]
  rfl

def equiv (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e) :
    letI := grading f hf
    Away (piece f) (chartCoordinate f) ≃+*
      AffineCurveFunctionField.CoordinateRing (NativeAffineChart.specialization F f) := by
  letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3) F) (ideal f)
    (PlaneCurveHilbert.ideal_homogeneous F f hf)
  letI := grading f hf
  exact (GradedQuotientChartMap.transportEquiv
    (HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin 3) F) (ideal f))
    (HomogeneousQuotientGrading.mk_surjective _ _) (isHomogeneous_X F (2 : Fin 3))
    (NativeAffineChart.originalEquiv F)).trans (Ideal.quotEquivOfEq (chartIdeal_eq f hf))

theorem chart_isDomain (f : MvPolynomial (Fin 3) F) [Fact (Irreducible f)] {e : ℕ}
    (hf : f.IsHomogeneous e) (hZ : X (2 : Fin 3) ∉ ideal f) :
    letI := grading f hf
    IsDomain (Away (piece f) (chartCoordinate f)) := by
  let := grading f hf
  apply ProjIntegral.localization_isDomain (piece f) (Submonoid.powers (chartCoordinate f))
  rintro ⟨n, hn⟩
  exact pow_ne_zero n (chartCoordinate_ne_zero f hZ) hn

theorem affineQuotient_isDomain (f : MvPolynomial (Fin 3) F) [Fact (Irreducible f)] {e : ℕ}
    (hf : f.IsHomogeneous e) (hZ : X (2 : Fin 3) ∉ ideal f) :
    IsDomain (AffineCurveFunctionField.CoordinateRing (NativeAffineChart.specialization F f)) := by
  let := grading f hf
  let := chart_isDomain f hf hZ
  exact (equiv f hf).symm.injective.isDomain (equiv f hf).symm.toRingHom

theorem specialization_ne_zero (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e)
    (hf0 : f ≠ 0) : NativeAffineChart.specialization F f ≠ 0 := by
  intro hz
  apply hf0
  apply GradedDehomogenizationPieces.homogeneous_eq_zero (homogeneousSubmodule (Fin 3) F)
    (isHomogeneous_X F (2 : Fin 3)) (MvPolynomial.X_ne_zero (2 : Fin 3)) e hf
  apply (NativeAffineChart.originalEquiv F).injective
  simpa only [NativeAffineChart.originalEquiv_dehomogenization, map_zero] using hz

theorem affine_irreducible (f : MvPolynomial (Fin 3) F) [h : Fact (Irreducible f)] {e : ℕ}
    (hf : f.IsHomogeneous e) (hZ : X (2 : Fin 3) ∉ ideal f) : Irreducible (NativeAffineChart.specialization F f) := by
  let := affineQuotient_isDomain f hf hZ
  have hp : (AffineCurveFunctionField.ideal (NativeAffineChart.specialization F f)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  exact ((Ideal.span_singleton_prime (specialization_ne_zero f hf h.out.ne_zero)).mp hp).irreducible

end PaperP1.HomogeneousAffinePrincipalChart
