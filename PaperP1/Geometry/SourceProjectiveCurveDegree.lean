module

public import PaperP1.Geometry.SourceCurveProjectivePointData
public import PaperP1.Geometry.SourceCurveHeightOneDegree

/-! # An actual height-one projective source point supplies its plane equation and curve degree

Primality, homogeneity, projective relevance, and a nonzero chart coordinate
are obtained from the projective point. No chart-coordinate witness is an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveDegree

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] [Infinite F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)

set_option linter.defProp false in
abbrev comparisonProof :=
  letI := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  SourceCurveProjectiveFieldRank.comparisonProof s c D I J hs hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg
    (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
    (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p)
    (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p)
    (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p)

include hs in
theorem exists_polynomial
    (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1) :
    ∃ q, GradedHilbertPolynomial.IsHilbertPolynomial
      (SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) q := by
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  exact SourceCurveHeightOneDegree.exists_polynomial_of_source_height s c D I J hs hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg
    (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
    (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p)
    (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p)
    (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p) hheight

theorem exists_degree_formula
    (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
        SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) =
          PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
        GradedHilbertPolynomial.multiplicity
          (SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
          (exists_polynomial s c D I J hs hdeg hD p hheight) = (D : ℚ) * (e : ℚ) * (m : ℚ))
      (comparisonProof s c D I J hs hdeg hD p) := by
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  exact SourceCurveHeightOneDegree.exists_degree_formula_of_source_height s c D I J hs hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg
    (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
    (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p)
    (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p)
    (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p) hheight

end PaperP1.SourceProjectiveCurveDegree
