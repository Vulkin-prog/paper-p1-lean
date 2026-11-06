module

public import PaperP1.Algebra.P3FactorSegreGrading
public import PaperP1.Geometry.ProjRadicalMap

/-! # The actual universal projective multiplication morphism on homogeneous coefficient families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorMultiplicationMap

open AlgebraicGeometry MvPolynomial P3HomogeneousCoefficientFamily P3FactorSegreGrading

attribute [local instance] MvPolynomial.gradedAlgebra P3FactorSegreGrading.grading

def sourceScheme (e f : ℕ) : Scheme := Proj (piece e f)

def coefficientScheme (d : ℕ) : Scheme := Proj (homogeneousSubmodule (Index d) ℤ)

def multiplication (e f : ℕ) : sourceScheme e f ⟶ coefficientScheme (e + f) :=
  ProjRadicalMap.map (gradedMap e f) (irrelevant_le_radical e f)

theorem preimage_basicOpen (e f : ℕ) (P : MvPolynomial (Index (e + f)) ℤ) :
    multiplication e f ⁻¹ᵁ ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Index (e + f)) ℤ) P =
      ProjectiveSpectrum.basicOpen (piece e f) (gradedMap e f P) :=
  ProjRadicalMap.map_preimage_basicOpen (gradedMap e f) (irrelevant_le_radical e f) P

end PaperP1.P3FactorMultiplicationMap
