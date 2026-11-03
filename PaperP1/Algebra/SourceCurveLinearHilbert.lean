module

public import PaperP1.Algebra.SourceCurveQuotient

/-! # An actual finite source curve quotient has an actual affine Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveLinearHilbert

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.SourceCurveQuotient

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))

local instance sourceQuotientRing : CommRing (SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseQuotientRing : CommRing (BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P
local instance sourceQuotientSemiring : Semiring (SourceRing s c D I J P) :=
  (sourceQuotientRing s c D I J P).toSemiring
local instance baseQuotientSemiring : Semiring (BaseRing s c D I J hs hD P) :=
  (baseQuotientRing s c D I J hs hD P).toSemiring

include hdeg hP

theorem hasSlope [P.IsPrime] (a b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (basePiece s c D I J hs hD P) (C a * X + C b)) :
    LinearHilbertGrowth.HasSlope (LinearHilbertGrowth.function (sourcePiece s c D I J P))
      ((rank s c D I J hs hD P : ℚ) * a) := by
  let : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    (ringMap s c D I J hs hD P).toAlgebra
  let := baseGrading s c D I J hs hD P hdeg hP
  let := sourceGrading s c D I J hD P hdeg hP
  have := base_domain s c D I J hs hD P
  have := source_domain s c D I J P
  exact FiniteGradedLinearGrowth.hasSlope (map s c D I J hs hD P)
    (map_commutes s c D I J hs hD P) (generator s c D I J hs hD P hdeg)
    (SourceCurveQuotient.weight s c D I J hdeg) (generator_mem s c D I J hs hD P hdeg)
    (map_injective s c D I J hs hD P) (generators_span s c D I J hs hD P hdeg)
    (base_piece_finite s c D I J hs hD P) a b hp

theorem affine_polynomial [P.IsPrime] (a b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (basePiece s c D I J hs hD P) (C a * X + C b))
    (hB : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (sourcePiece s c D I J P) p) :
    ∃ β : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial (sourcePiece s c D I J P)
      (C ((rank s c D I J hs hD P : ℚ) * a) * X + C β) := by
  obtain ⟨β, hβ⟩ := LinearHilbertGrowth.hilbert_polynomial_affine
    (hasSlope s c D I J hs hD P hdeg hP a b hp) hB.choose_spec
  exact ⟨β, hβ ▸ hB.choose_spec⟩

theorem affine_polynomial_multiplicity [P.IsPrime] (a b : ℚ) (ha : 0 < a)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (basePiece s c D I J hs hD P) (C a * X + C b))
    (hB : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (sourcePiece s c D I J P) p) :
    ∃ β : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial (sourcePiece s c D I J P)
      (C (GradedHilbertPolynomial.multiplicity (sourcePiece s c D I J P) hB) * X + C β) := by
  rw [SourceCurveQuotient.multiplicity s c D I J hs hD P hdeg hP a b ha hp hB]
  exact affine_polynomial s c D I J hs hD P hdeg hP a b hp hB

end PaperP1.SourceCurveLinearHilbert
