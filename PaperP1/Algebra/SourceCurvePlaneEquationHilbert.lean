module

public import PaperP1.Algebra.SourceCurveFiniteParameters
public import PaperP1.Algebra.NativePlaneQuotientNormalization
public import PaperP1.Algebra.PlaneCurveVeroneseBaseQuotient
public import PaperP1.Algebra.GradedQuotientIdealCongruence

/-! # Actual source curve Hilbert existence and degree over a plane-equation image

The actual base ideal is identified with the contracted plane equation.
Hilbert-polynomial existence is proved from this ideal equality, without
being supplied as a separate hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurvePlaneEquationHilbert

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] [Infinite F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  {e : ℕ} (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous e) (hf0 : f ≠ 0)
  (hbase : SourceCurveQuotient.baseIdeal s c D I J hs hD P = PlaneCurveVeroneseBaseQuotient.ideal F f D)

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P
local instance sourceQuotientSemiring : Semiring (SourceCurveQuotient.SourceRing s c D I J P) :=
  (sourceQuotientRing s c D I J P).toSemiring
local instance baseQuotientSemiring : Semiring (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  (baseQuotientRing s c D I J hs hD P).toSemiring

include hf hf0 hbase in
theorem base_hasParameters :
    FiniteGradedParameters.HasParameters (SourceCurveQuotient.basePiece s c D I J hs hD P) := by
  have hp := NativePlaneQuotientNormalization.hasParameters (HomogeneousPrincipalQuotient.ideal f)
    (PlaneCurveHilbert.ideal_homogeneous F f hf) D hD f hf hf0 (Ideal.mem_span_singleton_self f)
  exact GradedQuotientIdealCongruence.parameters (SourceVeroneseGrading.nativePiece F D) hbase.symm hp

include hf hf0 hbase hdeg in
theorem source_hasParameters :
    FiniteGradedParameters.HasParameters (SourceCurveQuotient.sourcePiece s c D I J P) :=
  SourceCurveFiniteParameters.hasParameters s c D I J hs hD P hdeg
    (base_hasParameters s c D I J hs hD P f hf hf0 hbase)

include hf hf0 hbase hdeg in
theorem exists_polynomial [P.IsPrime]
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.sourcePiece s c D I J P) p :=
  SourceCurveFiniteParameters.exists_polynomial s c D I J hs hD P hdeg hP
    (base_hasParameters s c D I J hs hD P f hf hf0 hbase)

include hf hf0 hbase in
omit [Infinite F] in
theorem base_isHilbertPolynomial :
    GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.basePiece s c D I J hs hD P)
      (Polynomial.C ((D : ℚ) * (e : ℚ)) * Polynomial.X +
        Polynomial.C ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)) := by
  have hp := PlaneCurveVeroneseBaseQuotient.affine_isHilbertPolynomial F f hf D hD hf0
  exact GradedQuotientIdealCongruence.hilbertPolynomial (SourceVeroneseGrading.nativePiece F D) hbase.symm hp

include hf hf0 hbase hdeg in
theorem multiplicity [P.IsPrime]
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) (he : 0 < e) :
    GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P)
      (exists_polynomial s c D I J hs hD P hdeg f hf hf0 hbase hP) =
        (SourceCurveQuotient.rank s c D I J hs hD P : ℚ) * ((D : ℚ) * (e : ℚ)) := by
  exact SourceCurveQuotient.multiplicity s c D I J hs hD P hdeg hP
    ((D : ℚ) * (e : ℚ)) ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)
    (mul_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr he))
    (base_isHilbertPolynomial s c D I J hs hD P f hf hf0 hbase)
    (exists_polynomial s c D I J hs hD P hdeg f hf hf0 hbase hP)

end PaperP1.SourceCurvePlaneEquationHilbert
