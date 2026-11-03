module

public import PaperP1.Geometry.SourceProjectiveCurveDegree
public import PaperP1.Geometry.ProjFunctionFieldRankOne

/-! # The actual degree-one projective curve field map is an isomorphism and reflects squares -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveFieldEquiv

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

/- The generic specialization infers the literal field and scalar instances.
Reconstructing them in a handwritten source-point return type makes Lean
compare large stalk-map transports. The inferred data type and the public
proposition extracted below preserve the exact checked instance expressions. -/
abbrev fieldEquiv
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p)) :=
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
  ProjFunctionFieldRankOne.equiv_of_module_rank_one
    (F := F) (A := SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (B := SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (G := SourceCurveQuotient.basePiece s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (H := SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveQuotient.map s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveProjectiveMap.admissible s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p))
    (SourceCurveProjectiveFieldRank.base_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p))
    (SourceCurveProjectiveFieldRank.source_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p))
    (SourceCurveQuotient.map_injective s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p)
    (SourceCurveQuotient.generator s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.weight s c D I J hdeg)
    (SourceCurveQuotient.generator_mem s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.generators_span s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (show Module.finrank (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) = 1 from
        (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p).symm.trans hdegree)

set_option linter.defProp false in
abbrev squareReflectionProof
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p)) :=
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
  ProjFunctionFieldRankOne.isSquare_iff_of_module_rank_one
    (F := F) (A := SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (B := SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (G := SourceCurveQuotient.basePiece s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (H := SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveQuotient.map s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceCurveProjectiveMap.admissible s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p))
    (SourceCurveProjectiveFieldRank.base_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p))
    (SourceCurveProjectiveFieldRank.source_nonempty s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p)
      (SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p))
    (SourceCurveQuotient.map_injective s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) (SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p) (SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p)
    (SourceCurveQuotient.generator s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.weight s c D I J hdeg)
    (SourceCurveQuotient.generator_mem s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (SourceCurveQuotient.generators_span s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg)
    (show Module.finrank (SourceCurveQuotient.BaseRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceCurveQuotient.SourceRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) = 1 from
        (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p).symm.trans hdegree)

theorem isSquare_iff
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p)) : beta%
    (fun {P : Prop} (_ : P) ↦ P) (squareReflectionProof s c D I J hs hdeg hD p hdegree) :=
  squareReflectionProof s c D I J hs hdeg hD p hdegree

end PaperP1.SourceProjectiveCurveFieldEquiv
