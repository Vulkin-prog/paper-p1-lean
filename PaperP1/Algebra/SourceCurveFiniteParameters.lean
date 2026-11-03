module

public import PaperP1.Algebra.SourceCurveQuotient
public import PaperP1.Algebra.FiniteGradedParameters

/-! # Actual source prime quotients inherit finite parameters and Hilbert existence from their base -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveFiniteParameters

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P
local instance sourceQuotientSemiring : Semiring (SourceCurveQuotient.SourceRing s c D I J P) :=
  (sourceQuotientRing s c D I J P).toSemiring
local instance baseQuotientSemiring : Semiring (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  (baseQuotientRing s c D I J hs hD P).toSemiring
local instance quotientModule [Algebra (SourceCurveQuotient.BaseRing s c D I J hs hD P)
    (SourceCurveQuotient.SourceRing s c D I J P)] :
    Module (SourceCurveQuotient.BaseRing s c D I J hs hD P) (SourceCurveQuotient.SourceRing s c D I J P) :=
  Algebra.toModule

def map : SourceCurveQuotient.BaseRing s c D I J hs hD P →ₐ[F]
    SourceCurveQuotient.SourceRing s c D I J P where
  __ := SourceCurveQuotient.ringMap s c D I J hs hD P
  commutes' a := SourceCurveQuotient.map_commutes s c D I J hs hD P a

include hdeg in
theorem finite : (map s c D I J hs hD P).Finite := by
  let : Algebra (SourceCurveQuotient.BaseRing s c D I J hs hD P)
      (SourceCurveQuotient.SourceRing s c D I J P) := (map s c D I J hs hD P).toRingHom.toAlgebra
  exact FreeApproximationRank.finite_of_span (SourceCurveQuotient.generator s c D I J hs hD P hdeg)
    (SourceCurveQuotient.generators_span s c D I J hs hD P hdeg)

include hdeg in
theorem hasParameters
    (hbase : FiniteGradedParameters.HasParameters (SourceCurveQuotient.basePiece s c D I J hs hD P)) :
    FiniteGradedParameters.HasParameters (SourceCurveQuotient.sourcePiece s c D I J P) := by
  exact FiniteGradedParameters.of_finite_map (SourceCurveQuotient.basePiece s c D I J hs hD P)
    (SourceCurveQuotient.sourcePiece s c D I J P) (map s c D I J hs hD P)
    (fun _ ha ↦ (SourceCurveQuotient.map s c D I J hs hD P).map_mem ha)
    (finite s c D I J hs hD P hdeg) hbase

include hs hD hdeg in
theorem exists_polynomial [P.IsPrime]
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))
    (hbase : FiniteGradedParameters.HasParameters (SourceCurveQuotient.basePiece s c D I J hs hD P)) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.sourcePiece s c D I J P) p := by
  let := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  let (n : ℕ) : Module.Finite F (SourceCurveQuotient.sourcePiece s c D I J P n) :=
    SourceCurveQuotient.source_piece_finite s c D I J hs hD P hdeg n
  have := SourceCurveQuotient.source_domain s c D I J P
  exact FiniteGradedParameters.exists_polynomial (SourceCurveQuotient.sourcePiece s c D I J P)
    (hasParameters s c D I J hs hD P hdeg hbase)

end PaperP1.SourceCurveFiniteParameters
