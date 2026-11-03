module

public import PaperP1.Algebra.SourceAffineChart
public import PaperP1.Algebra.NativeAffineChart
public import PaperP1.Algebra.RelativeVeroneseMap

/-! # The affine chart equivalence preserves the literal base coordinates and radical generators -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceAffineChartCoordinates

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalFiniteVeronese PaperP1.HomogeneousSplitRadicalChart
  PaperP1.HomogeneousSplitRadicalBaseInjection PaperP1.VeroneseCoordinateCharts

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))

def specialization : CoordinateRing c D I J →+*
    SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J :=
  (QuadraticTowerListCongr.congr F[X][X] (SourceAffineChart.affine_radicands s c D I J hs)).toRingHom.comp
    (HomogeneousSourceSpecialization.specialization s c D I J hs)

theorem equiv_dehomogenization (hD : 0 < D) (x : HomogeneousSplitRadicalVeronese.veronese c D I J) :
    letI := grading c D I J hdeg
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    SourceAffineChart.affineEquiv s c D I J hdeg hs hD
        (GradedDehomogenization.map (SourceVeroneseGrading.sourcePiece c D I J)
          (sourceCoordinate_mem c D I J hdeg 2) x) =
      specialization s c D I J hs (x : CoordinateRing c D I J) := by
  let := grading c D I J hdeg
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact congrArg (QuadraticTowerListCongr.congr F[X][X] (SourceAffineChart.affine_radicands s c D I J hs))
    (SourceAffineChart.veroneseEquiv_dehomogenization s c D I J hdeg hs hD x)

theorem specialization_base (p : MvPolynomial (Fin 3) F) :
    specialization s c D I J hs (basePolynomialMap c D I J p) =
      algebraMap F[X][X] (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J)
        (NativeAffineChart.specialization F p) := by
  change QuadraticTowerListCongr.congr F[X][X] (SourceAffineChart.affine_radicands s c D I J hs)
    ((QuadraticTowerBaseChange.mapData (chart F) s).hom
      (HomogeneousSplitRadicalPresentation.presentationEquiv s c D I J hs (basePolynomialMap c D I J p))) = _
  rw [presentationEquiv_base, QuadraticTowerBaseChange.MapData.commutes, QuadraticTowerListCongr.congr_base]
  rfl

theorem specialization_radical (i : Fin s.length) :
    specialization s c D I J hs (quotientMap c D I J (MvPolynomial.X (Sum.inr i))) =
      FiniteQuadraticTower.root F[X][X]
        (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
          ⟨i.val, by simpa only [SplitRadicalCoordinateAlgebra.radicands, List.length_map,
            List.length_finRange] using i.isLt⟩ := by
  change QuadraticTowerListCongr.congr F[X][X] (SourceAffineChart.affine_radicands s c D I J hs)
    ((QuadraticTowerBaseChange.mapData (chart F) s).hom
      (HomogeneousSplitRadicalPresentation.presentationEquiv s c D I J hs
        (quotientMap c D I J (MvPolynomial.X (Sum.inr i))))) = _
  rw [RelativeVeroneseMap.presentationEquiv_radical, QuadraticTowerGeneratorBaseChange.map_root,
    QuadraticTowerListCongr.congr_root]

theorem equiv_base (hD : 0 < D) (p : HomogeneousSplitRadicalVeroneseTowerData.Base F D) :
    letI := grading c D I J hdeg
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    SourceAffineChart.affineEquiv s c D I J hdeg hs hD
        (GradedDehomogenization.map (SourceVeroneseGrading.sourcePiece c D I J)
          (sourceCoordinate_mem c D I J hdeg 2)
            (standardBaseMap s c D hD I J hs p)) =
      algebraMap F[X][X] (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J)
        (NativeAffineChart.specialization F (p : MvPolynomial (Fin 3) F)) := by
  let := grading c D I J hdeg
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  rw [equiv_dehomogenization]
  exact specialization_base s c D I J hs p

theorem equiv_radical (hD : 0 < D) (i : Fin s.length) :
    letI := grading c D I J hdeg
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    SourceAffineChart.affineEquiv s c D I J hdeg hs hD
        (GradedDehomogenization.map (SourceVeroneseGrading.sourcePiece c D I J)
          (sourceCoordinate_mem c D I J hdeg 2) (radical c D I J i)) =
      FiniteQuadraticTower.root F[X][X]
        (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
          ⟨i.val, by simpa only [SplitRadicalCoordinateAlgebra.radicands, List.length_map,
            List.length_finRange] using i.isLt⟩ := by
  let := grading c D I J hdeg
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  rw [equiv_dehomogenization]
  exact specialization_radical s c D I J hs i

end PaperP1.SourceAffineChartCoordinates
