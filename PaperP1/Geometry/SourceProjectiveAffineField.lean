module

public import PaperP1.Geometry.ProjAffineFieldEquiv
public import PaperP1.Geometry.SourceProjectiveFunctionField
public import PaperP1.Algebra.SourceAffineChartCoordinates
public import PaperP1.Algebra.BirationalRadicalProjection
public import PaperP1.Algebra.SplitRadicalProjectionPolynomial

/-! # Actual projective function fields are the explicit affine generic split-radical fields -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveAffineField

open AlgebraicGeometry Polynomial PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.SourceVeroneseGrading
  PaperP1.SourceProjectiveIntegral PaperP1.StandardVeroneseCoordinates
  PaperP1.VeroneseCoordinateCharts

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type u) [Field F] : CommRing F[X][X] := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

def baseEquiv (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := base_integral F D hD
    (SourceProjectiveMap.baseScheme F D hD).functionField ≃+* ScaledSplitWordSquares.FunctionField F := by
  let := nativeGrading F D hD
  let := base_integral F D hD
  exact ProjAffineFieldEquiv.equiv (nativePiece F D) (base_irrelevant_ne_bot F D hD)
    (coordinatePower_mem F D 2) (coordinatePower_ne_zero F D 2) (NativeAffineChart.equiv F D hD)

theorem baseEquiv_chartMap (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := nativeGrading F D hD
    letI := base_integral F D hD
    ∀ z : HomogeneousLocalization.Away (nativePiece F D) (coordinatePower F D 2),
      baseEquiv F D hD
          (ProjChartFunctionField.chartMap (nativePiece F D) (base_irrelevant_ne_bot F D hD)
            (coordinatePower_ne_zero F D 2) z) =
        algebraMap F[X][X] (ScaledSplitWordSquares.FunctionField F) (NativeAffineChart.equiv F D hD z) := by
  let := nativeGrading F D hD
  let := base_integral F D hD
  exact ProjAffineFieldEquiv.equiv_chartMap (nativePiece F D) (base_irrelevant_ne_bot F D hD)
    (coordinatePower_mem F D 2) (coordinatePower_ne_zero F D 2) (NativeAffineChart.equiv F D hD)

abbrev AffineRing {F : Type u} [Field F] (k : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ) :=
  SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange k) c I J

abbrev GenericField {F : Type u} [Field F] (k : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ) :=
  BirationalRadicalProjection.GenericTower F[X][X] (ScaledSplitWordSquares.FunctionField F)
    (SplitRadicalCoordinateAlgebra.radicands (List.finRange k) c I J)

def affineGenericMap {F : Type u} [Field F] (k : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ) :
    AffineRing k c I J →+* GenericField k c I J :=
  BirationalRadicalProjection.genericMap F[X][X] (ScaledSplitWordSquares.FunctionField F)
    (SplitRadicalCoordinateAlgebra.radicands (List.finRange k) c I J)

theorem affineGenericMap_commutes {F : Type u} [Field F] (k : ℕ) (c : Fin k → F)
    (I J : Fin k → Finset ℤ) (r : F[X][X]) :
    affineGenericMap k c I J (algebraMap F[X][X] (AffineRing k c I J) r) =
      algebraMap (ScaledSplitWordSquares.FunctionField F) (GenericField k c I J)
        (algebraMap F[X][X] (ScaledSplitWordSquares.FunctionField F) r) :=
  (QuadraticTowerBaseChange.mapData
    (algebraMap F[X][X] (ScaledSplitWordSquares.FunctionField F))
      (SplitRadicalCoordinateAlgebra.radicands (List.finRange k) c I J)).commutes r

variable {F : Type u} [Field F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

include hs hD in
theorem sourceCoordinate_ne_zero : sourceCoordinate c D I J hdeg (2 : Fin 3) ≠ 0 := by
  rw [sourceCoordinate_eq_image s c D I J hdeg hD hs]
  intro hz
  apply coordinatePower_ne_zero F D 2
  apply SourceVeroneseGradedBaseMap.gradedBaseMap_injective s c D hD I J hs
  exact hz.trans (map_zero (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs)).symm

variable [CharZero F]
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))

def sourceEquiv :
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    (SourceProjectiveMap.sourceScheme c D I J hdeg hD).functionField ≃+*
      GenericField s.length c I J := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  let : Algebra (AffineRing s.length c I J) (GenericField s.length c I J) :=
    (affineGenericMap s.length c I J).toAlgebra
  have : IsFractionRing (AffineRing s.length c I J) (GenericField s.length c I J) :=
    BirationalRadicalProjection.source_isFractionRing F[X][X] (ScaledSplitWordSquares.FunctionField F)
      (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
      (SplitRadicalProjectionPolynomial.generic_independent (List.finRange s.length)
        (List.nodup_finRange _) c hc I J hne hI hJ)
  exact ProjAffineFieldEquiv.equiv (sourcePiece c D I J)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg) (sourceCoordinate_mem c D I J hdeg 2)
    (sourceCoordinate_ne_zero s c D hD I J hs hdeg) (SourceAffineChart.affineEquiv s c D I J hdeg hs hD)

theorem sourceEquiv_chartMap :
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    ∀ z : HomogeneousLocalization.Away (sourcePiece c D I J) (sourceCoordinate c D I J hdeg 2),
      sourceEquiv s c D hD I J hs hdeg hc hne hI hJ
          (ProjChartFunctionField.chartMap (sourcePiece c D I J)
            (source_irrelevant_ne_bot s c D hD I J hs hdeg)
            (sourceCoordinate_ne_zero s c D hD I J hs hdeg) z) =
        affineGenericMap s.length c I J (SourceAffineChart.affineEquiv s c D I J hdeg hs hD z) := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  let : Algebra (AffineRing s.length c I J) (GenericField s.length c I J) :=
    (affineGenericMap s.length c I J).toAlgebra
  have : IsFractionRing (AffineRing s.length c I J) (GenericField s.length c I J) :=
    BirationalRadicalProjection.source_isFractionRing F[X][X] (ScaledSplitWordSquares.FunctionField F)
      (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
      (SplitRadicalProjectionPolynomial.generic_independent (List.finRange s.length)
        (List.nodup_finRange _) c hc I J hne hI hJ)
  exact ProjAffineFieldEquiv.equiv_chartMap (sourcePiece c D I J)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg) (sourceCoordinate_mem c D I J hdeg 2)
    (sourceCoordinate_ne_zero s c D hD I J hs hdeg) (SourceAffineChart.affineEquiv s c D I J hdeg hs hD)

end PaperP1.SourceProjectiveAffineField
