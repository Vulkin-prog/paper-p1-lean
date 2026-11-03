module

public import PaperP1.Geometry.SourceCurvePlaneImagePrime
public import PaperP1.Algebra.HomogeneousHeightOneEquation
public import PaperP1.Algebra.PlaneCurveVeroneseBaseQuotient

/-! # Extracting a homogeneous irreducible plane equation from the actual height-one image prime -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurvePlaneImageEquation

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))
  (b : SourceCurveQuotient.BaseRing s c D I J hs hD P)
  (hb : b ∈ SourceCurveQuotient.basePiece s c D I J hs hD P 1) (hb0 : b ≠ 0)

local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P

theorem exists_equation [P.IsPrime]
    (hh : (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).height = 1) :
    ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
      SourceCurveQuotient.baseIdeal s c D I J hs hD P = PlaneCurveVeroneseBaseQuotient.ideal F f D := by
  have hprime := SourceCurvePlaneImagePrime.ideal_prime s c D I J hs hD P hdeg hP b hb hb0
  obtain ⟨e, f, he, hf0, hf, hspan⟩ := HomogeneousHeightOneEquation.exists_equation
    (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0)
    (SourceCurvePlaneImagePrime.ideal_homogeneous s c D I J hs hD P hdeg hP b hb hb0) hh
  have hfprime : Prime f := (Ideal.span_singleton_prime hf0).mp (hspan ▸ hprime)
  refine ⟨e, f, he, hf0, hf, hfprime.irreducible, ?_⟩
  change SourceCurveQuotient.baseIdeal s c D I J hs hD P =
    (Ideal.span {f}).comap (StandardBaseVeronese.nativeVeronese F D).val.toRingHom
  rw [← hspan]
  exact (SourceCurvePlaneImagePrime.contraction s c D I J hs hD P hdeg hP b hb hb0).symm

end PaperP1.SourceCurvePlaneImageEquation
