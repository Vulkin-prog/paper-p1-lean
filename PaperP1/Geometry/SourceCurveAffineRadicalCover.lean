module

public import PaperP1.Geometry.ProjChartRadicalCover
public import PaperP1.Geometry.SourceCurveProjectiveFieldRank
public import PaperP1.Algebra.NativeVeroneseQuotientChart
public import PaperP1.Algebra.SourceCurveRadicalRelations
public import PaperP1.Algebra.AffineCurveFunctionField

/-! # The actual radical source prime quotient constructs a finite cover of its actual affine curve function field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveAffineRadicalCover

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance affineRing (F : Type u) [Field F] : CommRing F[X][X] := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hD : 0 < D) (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))
  (g : F[X][X]) [Fact (Irreducible g)]
  (himage : NativeVeroneseAffineIdeal.affineIdeal F D (SourceCurveQuotient.baseIdeal s c D I J hs hD P) =
    AffineCurveFunctionField.ideal g)

local instance sourceRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P
local instance affineCoordinateRing : CommRing (AffineCurveFunctionField.CoordinateRing g) := inferInstance

def chartEquiv :
    letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
    Away (SourceCurveQuotient.basePiece s c D I J hs hD P)
      (Ideal.Quotient.mk (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
        (StandardVeroneseCoordinates.coordinatePower F D 2)) ≃+* AffineCurveFunctionField.CoordinateRing g := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D)
    (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
    (SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD P hdeg hP)
  letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  exact (NativeVeroneseQuotientChart.equiv F D hD (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
    (SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD P hdeg hP)).trans (Ideal.quotEquivOfEq himage)

omit [Fact (Irreducible g)] in
theorem chartEquiv_radicand (i : Fin s.length) :
    letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
    chartEquiv s c D I J hs hD P hdeg hP g himage
      (GradedDehomogenization.map (SourceCurveQuotient.basePiece s c D I J hs hD P)
        ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D)
          (SourceCurveQuotient.baseIdeal s c D I J hs hD P)).map_mem (StandardVeroneseCoordinates.coordinatePower_mem F D 2))
        (SourceCurveRadicalRelations.baseRadicand s c D I J hs hD P hdeg i)) =
      Ideal.Quotient.mk (AffineCurveFunctionField.ideal g) (ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i)) := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D)
    (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
    (SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD P hdeg hP)
  let := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  have he := NativeVeroneseQuotientChart.equiv_dehomogenization F D hD
    (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
    (SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD P hdeg hP)
    (HomogeneousSplitRadicalVeroneseTowerData.baseRadicand (c i) D (I i) (J i) (hdeg i))
  have h := congrArg (Ideal.quotEquivOfEq himage) he
  exact h.trans (congrArg (Ideal.Quotient.mk (AffineCurveFunctionField.ideal g))
    (NativeVeroneseAffineIdeal.affineMap_radicand (c i) D (I i) (J i) (hdeg i)))

include hdeg hP himage in
theorem exists_cover [P.IsPrime]
    (hZ : Ideal.Quotient.mk (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
      (StandardVeroneseCoordinates.coordinatePower F D 2) ≠ 0) :
    ∃ (L : Type u) (inst : Field L), letI := inst
      ∃ alg : Algebra (AffineCurveFunctionField.FunctionField g) L, letI := alg
        Module.Finite (AffineCurveFunctionField.FunctionField g) L ∧
        Module.finrank (AffineCurveFunctionField.FunctionField g) L = SourceCurveQuotient.rank s c D I J hs hD P ∧
        ∃ r : Fin s.length → L, ∀ i, r i ^ 2 = algebraMap (AffineCurveFunctionField.FunctionField g) L
          (AffineCurveFunctionField.specialize g (ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i))) := by
  let := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  let := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  let := SourceCurveQuotient.base_domain s c D I J hs hD P
  let := SourceCurveQuotient.source_domain s c D I J P
  let b := Ideal.Quotient.mk (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
    (StandardVeroneseCoordinates.coordinatePower F D 2)
  have hb : b ∈ SourceCurveQuotient.basePiece s c D I J hs hD P 1 :=
    (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D)
      (SourceCurveQuotient.baseIdeal s c D I J hs hD P)).map_mem (StandardVeroneseCoordinates.coordinatePower_mem F D 2)
  obtain ⟨L, instL, algL, hfinite, hdegree, r, hr⟩ := ProjChartRadicalCover.exists_cover
    (F := F) (A := SourceCurveQuotient.BaseRing s c D I J hs hD P)
    (B := SourceCurveQuotient.SourceRing s c D I J P) (R := AffineCurveFunctionField.CoordinateRing g)
    (G := SourceCurveQuotient.basePiece s c D I J hs hD P) (H := SourceCurveQuotient.sourcePiece s c D I J P)
    (SourceCurveQuotient.map s c D I J hs hD P) (SourceCurveProjectiveMap.admissible s c D I J hs hD P hdeg hP)
    (SourceCurveProjectiveFieldRank.base_nonempty s c D I J hs hD P hdeg hP b hb hZ)
    (SourceCurveProjectiveFieldRank.source_nonempty s c D I J hs hD P hdeg hP b hb hZ)
    (SourceCurveQuotient.map_injective s c D I J hs hD P) hb hZ
    (SourceCurveQuotient.generator s c D I J hs hD P hdeg) (SourceCurveQuotient.weight s c D I J hdeg)
    (SourceCurveQuotient.generator_mem s c D I J hs hD P hdeg)
    (chartEquiv s c D I J hs hD P hdeg hP g himage)
    (SourceCurveQuotient.generators_span s c D I J hs hD P hdeg)
    (SourceCurveRadicalRelations.baseRadicand s c D I J hs hD P hdeg)
    (SourceCurveRadicalRelations.root s c D I J P) (SourceCurveRadicalRelations.root_square s c D I J hs hD P hdeg)
  let := instL
  let := algL
  refine ⟨L, instL, algL, hfinite, hdegree, r, ?_⟩
  intro i
  have hc := congrArg (fun z : AffineCurveFunctionField.CoordinateRing g ↦
    algebraMap (AffineCurveFunctionField.FunctionField g) L
      (algebraMap (AffineCurveFunctionField.CoordinateRing g) (AffineCurveFunctionField.FunctionField g) z))
    (chartEquiv_radicand s c D I J hs hD P hdeg hP g himage i)
  exact (hr i).trans hc

end PaperP1.SourceCurveAffineRadicalCover
