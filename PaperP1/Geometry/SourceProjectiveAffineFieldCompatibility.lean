module

public import PaperP1.Geometry.SourceProjectiveAffineField
public import PaperP1.Geometry.ProjChartDehomogenizationNaturality
public import PaperP1.Geometry.SourceProjectiveFunctionFieldCompatibility

/-! # The explicit affine field identifications commute with the actual projective field map -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveAffineFieldCompatibility

open AlgebraicGeometry Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant
  PaperP1.SourceProjectiveIntegral PaperP1.StandardVeroneseCoordinates PaperP1.VeroneseCoordinateCharts
  PaperP1.SourceProjectiveAffineField

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type u) [Field F] : CommRing F[X][X] := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] [CharZero F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))

theorem chart_dehomogenization_natural (p : Base F D) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    SourceProjectiveFunctionField.map s c D hD I J hs hdeg hc hne hI hJ
        (ProjChartFunctionField.chartMap (nativePiece F D) (base_irrelevant_ne_bot F D hD)
          (coordinatePower_ne_zero F D 2)
            (GradedDehomogenization.map (nativePiece F D) (coordinatePower_mem F D 2) p)) =
      ProjChartFunctionField.chartMap (sourcePiece c D I J)
        (source_irrelevant_ne_bot s c D hD I J hs hdeg)
        (sourceCoordinate_ne_zero s c D hD I J hs hdeg)
          (GradedDehomogenization.map (sourcePiece c D I J) (sourceCoordinate_mem c D I J hdeg 2)
            (gradedBaseMap s c D hD I J hs p)) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  have hfb0 : gradedBaseMap s c D hD I J hs (coordinatePower F D 2) ≠ 0 := by
    rw [← sourceCoordinate_eq_image s c D I J hdeg hD hs]
    exact sourceCoordinate_ne_zero s c D hD I J hs hdeg
  exact (ProjChartDehomogenizationNaturality.dehomogenization_natural (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg) (base_irrelevant_ne_bot F D hD)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg) (gradedBaseMap_injective s c D hD I J hs)
    (coordinatePower_mem F D 2) (coordinatePower_ne_zero F D 2) hfb0 p).trans
      (ProjChartDehomogenizationNaturality.chart_dehomogenization_congr (sourcePiece c D I J)
        (source_irrelevant_ne_bot s c D hD I J hs hdeg)
        ((gradedBaseMap s c D hD I J hs).map_mem (coordinatePower_mem F D 2))
        (sourceCoordinate_mem c D I J hdeg 2) hfb0 (sourceCoordinate_ne_zero s c D hD I J hs hdeg)
        (sourceCoordinate_eq_image s c D I J hdeg hD hs 2).symm (gradedBaseMap s c D hD I J hs p))

set_option backward.isDefEq.respectTransparency false in
theorem equiv_comp_map :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    (sourceEquiv s c D hD I J hs hdeg hc hne hI hJ).toRingHom.comp
        (SourceProjectiveFunctionField.map s c D hD I J hs hdeg hc hne hI hJ) =
      (algebraMap (ScaledSplitWordSquares.FunctionField F) (GenericField s.length c I J)).comp
        (baseEquiv F D hD).toRingHom := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  let : Algebra (Away (nativePiece F D) (coordinatePower F D 2))
      (SourceProjectiveMap.baseScheme F D hD).functionField :=
    (ProjChartFunctionField.chartMap (nativePiece F D) (base_irrelevant_ne_bot F D hD)
      (coordinatePower_ne_zero F D 2)).toAlgebra
  have : IsFractionRing (Away (nativePiece F D) (coordinatePower F D 2))
      (SourceProjectiveMap.baseScheme F D hD).functionField :=
    ProjChartFunctionField.chart_isFractionRing (nativePiece F D) (base_irrelevant_ne_bot F D hD)
      (coordinatePower_ne_zero F D 2) (coordinatePower_mem F D 2)
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Away (nativePiece F D) (coordinatePower F D 2)))
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := GradedDehomogenization.map_surjective (nativePiece F D) (coordinatePower_mem F D 2) z
  change sourceEquiv s c D hD I J hs hdeg hc hne hI hJ
    (SourceProjectiveFunctionField.map s c D hD I J hs hdeg hc hne hI hJ
      (ProjChartFunctionField.chartMap (nativePiece F D) (base_irrelevant_ne_bot F D hD)
        (coordinatePower_ne_zero F D 2)
          (GradedDehomogenization.map (nativePiece F D) (coordinatePower_mem F D 2) p))) =
    algebraMap (ScaledSplitWordSquares.FunctionField F) (GenericField s.length c I J)
      (baseEquiv F D hD
        (ProjChartFunctionField.chartMap (nativePiece F D) (base_irrelevant_ne_bot F D hD)
          (coordinatePower_ne_zero F D 2)
            (GradedDehomogenization.map (nativePiece F D) (coordinatePower_mem F D 2) p)))
  rw [chart_dehomogenization_natural, sourceEquiv_chartMap]
  have hp := SourceAffineChartCoordinates.equiv_base s c D I J hdeg hs hD p
  apply (congrArg (affineGenericMap s.length c I J) hp).trans
  rw [affineGenericMap_commutes, baseEquiv_chartMap, NativeAffineChart.equiv_dehomogenization]

end PaperP1.SourceProjectiveAffineFieldCompatibility
