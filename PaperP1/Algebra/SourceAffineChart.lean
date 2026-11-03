module

public import PaperP1.Algebra.HomogeneousSourceSpecialization
public import PaperP1.Algebra.QuadraticTowerListCongr

/-! # The literal Z-chart of the actual source is the paper's affine split-radical algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceAffineChart

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalChart PaperP1.VeroneseCoordinateCharts

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))

include hs in
theorem affine_radicands : s.map (chart F) =
    SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J := by
  calc
    s.map (chart F) = (List.ofFn s.get).map (chart F) := by rw [List.ofFn_get]
    _ = List.ofFn (fun i ↦ ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i)) := by
      rw [List.map_ofFn]
      congr 1
      funext i
      dsimp only [Function.comp_apply]
      rw [hs i, radicand_chart]
    _ = _ := List.ofFn_eq_map

def originalEquiv :
    letI := grading c D I J hdeg
    Away (piece c D I J) (baseVariable c D I J (2 : Fin 3)) ≃+*
      FiniteQuadraticTower.Tower F[X][X] (s.map (chart F)) := by
  let := grading c D I J hdeg
  exact (GradedDehomogenizationQuotient.equiv (piece c D I J) (base_variable_mem c D I J 2)).symm.trans
    (HomogeneousSourceSpecialization.quotientEquiv s c D I J hs)

theorem originalEquiv_dehomogenization (x : CoordinateRing c D I J) :
    letI := grading c D I J hdeg
    originalEquiv s c D I J hdeg hs
        (GradedDehomogenization.map (piece c D I J) (base_variable_mem c D I J 2) x) =
      HomogeneousSourceSpecialization.specialization s c D I J hs x := by
  let := grading c D I J hdeg
  change HomogeneousSourceSpecialization.quotientEquiv s c D I J hs
    ((GradedDehomogenizationQuotient.equiv (piece c D I J) (base_variable_mem c D I J 2)).symm
      (GradedDehomogenization.map (piece c D I J) (base_variable_mem c D I J 2) x)) = _
  rw [← GradedDehomogenizationQuotient.equiv_mk, RingEquiv.symm_apply_apply]
  exact HomogeneousSourceSpecialization.quotientEquiv_mk s c D I J hs x

def veroneseEquiv (hD : 0 < D) :
    letI := grading c D I J hdeg
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    Away (SourceVeroneseGrading.sourcePiece c D I J) (sourceCoordinate c D I J hdeg 2) ≃+*
      FiniteQuadraticTower.Tower F[X][X] (s.map (chart F)) := by
  let := grading c D I J hdeg
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact (sourceEquiv c D I J hdeg hD 2).trans (originalEquiv s c D I J hdeg hs)

theorem veroneseEquiv_dehomogenization (hD : 0 < D) (x : HomogeneousSplitRadicalVeronese.veronese c D I J) :
    letI := grading c D I J hdeg
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    veroneseEquiv s c D I J hdeg hs hD
        (GradedDehomogenization.map (SourceVeroneseGrading.sourcePiece c D I J)
          (sourceCoordinate_mem c D I J hdeg 2) x) =
      HomogeneousSourceSpecialization.specialization s c D I J hs (x : CoordinateRing c D I J) := by
  let := grading c D I J hdeg
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  change originalEquiv s c D I J hdeg hs
    (GradedVeroneseChart.map (piece c D I J) D hD (base_variable_mem c D I J 2)
      (GradedDehomogenization.map (SourceVeroneseGrading.sourcePiece c D I J)
        (sourceCoordinate_mem c D I J hdeg 2) x)) = _
  exact (congrArg (originalEquiv s c D I J hdeg hs)
    (GradedVeroneseChart.map_dehomogenization (piece c D I J) D hD
      (base_variable_mem c D I J 2) x)).trans
        (originalEquiv_dehomogenization s c D I J hdeg hs x)

def affineEquiv (hD : 0 < D) :
    letI := grading c D I J hdeg
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    Away (SourceVeroneseGrading.sourcePiece c D I J) (sourceCoordinate c D I J hdeg 2) ≃+*
      SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J := by
  let := grading c D I J hdeg
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact (veroneseEquiv s c D I J hdeg hs hD).trans
    (QuadraticTowerListCongr.congr F[X][X] (affine_radicands s c D I J hs)).toRingEquiv

end PaperP1.SourceAffineChart
