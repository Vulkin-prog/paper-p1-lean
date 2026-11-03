module

public import PaperP1.Geometry.SourceProjectiveCurveDegree
public import PaperP1.Geometry.ProjRankOneQuadraticDescent
public import PaperP1.Algebra.SourceCurveRadicalRelations

/-! # Actual source-curve radical equations descend to its degree-one base field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveRadicalDescent

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


variable (b : SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
  (hb : b ∈ SourceCurveQuotient.basePiece s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) 1) (hb0 : b ≠ 0)

set_option linter.defProp false in
abbrev radicalSquareProof
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p)) (i : Fin s.length) :=
  letI := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  letI := SourceCurveQuotient.baseGrading s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
  letI := SourceCurveQuotient.sourceGrading s c D I J hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
  letI := SourceCurveQuotient.base_domain s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
  letI := SourceCurveQuotient.source_domain s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
  letI : Algebra (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
    (SourceCurveQuotient.map s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)).toRingHom.toAlgebra
  letI : Module (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) := Algebra.toModule
  ProjRankOneQuadraticDescent.dehomogenized_isSquare
    (F := F) (A := SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (B := SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (G := SourceCurveQuotient.basePiece s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (H := SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveQuotient.map s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveProjectiveMap.admissible s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p))
    (SourceCurveProjectiveFieldRank.base_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      b hb hb0)
    (SourceCurveProjectiveFieldRank.source_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      b hb hb0)
    (SourceCurveQuotient.map_injective s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) hb hb0
    (SourceCurveQuotient.generator s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.weight s c D I J hdeg)
    (SourceCurveQuotient.generator_mem s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.generators_span s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (show Module.finrank (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) = 1 from
        (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p).symm.trans hdegree)

    (SourceCurveRadicalRelations.baseRadicand s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg i)
    (SourceCurveRadicalRelations.root s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) i)
    (SourceCurveRadicalRelations.root_square s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg i)

theorem radical_isSquare
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p)) (i : Fin s.length) : beta%
    (fun {P : Prop} (_ : P) ↦ P) (radicalSquareProof s c D I J hs hdeg hD p b hb hb0 hdegree i) :=
  radicalSquareProof s c D I J hs hdeg hD p b hb hb0 hdegree i

end PaperP1.SourceProjectiveCurveRadicalDescent
