module

public import PaperP1.Geometry.SourceProjectiveCurveDegree
public import PaperP1.Geometry.ProjOddDegreeQuadraticDescent
public import PaperP1.Algebra.SourceCurveRadicalRelations
public import PaperP1.Algebra.NativeVeroneseVerticalChart

/-! # Actual odd-degree source-curve projections give literal functional squares on a vertical line -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveVerticalSquares

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
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


theorem verticalRestriction_isSquare_of_odd_degree
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ Odd m)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p))
    (γ : F)
    (hline : NativeVeroneseAffineIdeal.affineIdeal F D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) =
      Ideal.span {NativeVeroneseVerticalChart.equation γ})
    (i : Fin s.length) :
    IsSquare (algebraMap (Polynomial F) (FractionRing (Polynomial F))
      (Polynomial.C (c i) * Polynomial.C ((FormalWordPolynomials.linearOver F (I i)).eval γ) *
        FormalWordPolynomials.linearOver F (J i))) := by
  have hZ := NativeVeroneseVerticalChart.coordinate_ne_zero D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) γ hline
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  let := SourceCurveQuotient.baseGrading s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
  let := SourceCurveQuotient.sourceGrading s c D I J hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
  let := SourceCurveQuotient.base_domain s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
  let := SourceCurveQuotient.source_domain s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
  let : Algebra (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
    (SourceCurveQuotient.map s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)).toRingHom.toAlgebra
  let : Module (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) := Algebra.toModule
  have h := ProjOddDegreeQuadraticDescent.parametrized_isSquare
    (F := F) (A := SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (B := SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (G := SourceCurveQuotient.basePiece s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (H := SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveQuotient.map s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveProjectiveMap.admissible s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p))
    (SourceCurveProjectiveFieldRank.base_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      (Ideal.Quotient.mk (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) (StandardVeroneseCoordinates.coordinatePower F D 2)) ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))).map_mem (StandardVeroneseCoordinates.coordinatePower_mem F D 2)) hZ)
    (SourceCurveProjectiveFieldRank.source_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      (Ideal.Quotient.mk (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) (StandardVeroneseCoordinates.coordinatePower F D 2)) ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))).map_mem (StandardVeroneseCoordinates.coordinatePower_mem F D 2)) hZ)
    (SourceCurveQuotient.map_injective s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))).map_mem (StandardVeroneseCoordinates.coordinatePower_mem F D 2)) hZ
    (SourceCurveQuotient.generator s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.weight s c D I J hdeg)
    (SourceCurveQuotient.generator_mem s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.generators_span s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (show Odd (Module.finrank (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))) from
        (congrArg Odd (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p)).mp hdegree)

    (SourceCurveRadicalRelations.baseRadicand s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg i)
    (SourceCurveRadicalRelations.root s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) i)
    (SourceCurveRadicalRelations.root_square s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg i)
    (NativeVeroneseVerticalChart.equiv D hD (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) (SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)) γ hline)
  have he := NativeVeroneseVerticalChart.equiv_radicand D hD (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) (SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)) γ hline (c i) (I i) (J i) (hdeg i)
  exact (congrArg (fun x : Polynomial F ↦ IsSquare (algebraMap (Polynomial F) (FractionRing (Polynomial F)) x)) he).mp h

theorem verticalRestriction_isSquare
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p))
    (γ : F)
    (hline : NativeVeroneseAffineIdeal.affineIdeal F D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) =
      Ideal.span {NativeVeroneseVerticalChart.equation γ})
    (i : Fin s.length) :
    IsSquare (algebraMap (Polynomial F) (FractionRing (Polynomial F))
      (Polynomial.C (c i) * Polynomial.C ((FormalWordPolynomials.linearOver F (I i)).eval γ) *
        FormalWordPolynomials.linearOver F (J i))) := by
  exact verticalRestriction_isSquare_of_odd_degree s c D I J hs hdeg hD p
    (hdegree.symm ▸ (by decide : Odd (1 : ℕ))) γ hline i

end PaperP1.SourceProjectiveCurveVerticalSquares
