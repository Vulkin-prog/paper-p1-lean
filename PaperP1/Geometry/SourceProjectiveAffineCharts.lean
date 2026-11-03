module

public import PaperP1.Algebra.SourceAffineChartCoordinates
public import PaperP1.Geometry.SourceProjectiveMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # The actual projective Z-charts are the spectra of the literal affine rings -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveAffineCharts

open AlgebraicGeometry CategoryTheory Polynomial PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.SourceVeroneseGrading
  PaperP1.StandardVeroneseCoordinates PaperP1.VeroneseCoordinateCharts

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type u) [Field F] : CommRing F[X][X] := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

def baseChartIso (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := nativeGrading F D hD
    (Proj.basicOpen (nativePiece F D) (coordinatePower F D 2)).toScheme ≅ Spec (CommRingCat.of F[X][X]) := by
  let := nativeGrading F D hD
  exact Proj.basicOpenIsoSpec (nativePiece F D) (coordinatePower F D 2)
    (coordinatePower_mem F D 2) (by decide : 0 < 1) ≪≫
      Scheme.Spec.mapIso (NativeAffineChart.equiv F D hD).symm.toCommRingCatIso.op

def sourceChartIso {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (I J : Fin s.length → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D) :
    letI := HomogeneousSplitRadicalGrading.grading c D I J hdeg
    letI := sourceGrading c D I J hdeg hD
    (Proj.basicOpen (sourcePiece c D I J) (sourceCoordinate c D I J hdeg 2)).toScheme ≅
      Spec (CommRingCat.of (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J)) := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let := sourceGrading c D I J hdeg hD
  exact Proj.basicOpenIsoSpec (sourcePiece c D I J) (sourceCoordinate c D I J hdeg 2)
    (sourceCoordinate_mem c D I J hdeg 2) (by decide : 0 < 1) ≪≫
      Scheme.Spec.mapIso (SourceAffineChart.affineEquiv s c D I J hdeg hs hD).symm.toCommRingCatIso.op

end PaperP1.SourceProjectiveAffineCharts
