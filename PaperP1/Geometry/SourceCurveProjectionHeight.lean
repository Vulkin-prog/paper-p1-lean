module

public import PaperP1.Geometry.SourceCurvePlaneImagePrime
public import PaperP1.Algebra.IntegralPrimeHeight
public import PaperP1.Algebra.GradedVeroneseIntegral

/-! # The actual finite free projection preserves prime height and its plane image has height one -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveProjectionHeight

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

include hdeg in
theorem base_height [P.IsPrime] : (SourceCurveQuotient.baseIdeal s c D I J hs hD P).height = P.height := by
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs).toRingHom.toAlgebra
  let : Module (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) := Algebra.toModule
  have hb := RelativeVeroneseBasis.source_free_rank s c D I J hdeg hs hD
  have : Module.Free (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) := hb.1
  have : Module.Finite (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) := hb.2.1
  have : Module.Flat (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) := inferInstance
  have : Algebra.IsIntegral (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) := inferInstance
  exact (IntegralPrimeHeight.height_eq (R := Base F D) P).symm

theorem plane_height_le [P.IsPrime] :
    (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).height ≤ P.height := by
  have := SourceCurvePlaneImagePrime.ideal_prime s c D I J hs hD P hdeg hP b hb hb0
  have : Algebra.IsIntegral (Base F D) (MvPolynomial (Fin 3) F) :=
    GradedVeroneseIntegral.integral (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD
  have h := IntegralPrimeHeight.height_le (R := Base F D)
    (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0)
  change (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).height ≤
    ((SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).comap
      (StandardBaseVeronese.nativeVeronese F D).val.toRingHom).height at h
  rw [SourceCurvePlaneImagePrime.contraction, base_height s c D I J hs hD P hdeg] at h
  exact h

theorem plane_height_one [P.IsPrime] (hsource : P.height = 1) :
    (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).height = 1 := by
  have hbase := (base_height s c D I J hs hD P hdeg).trans hsource
  have hQ0 : SourceCurveQuotient.baseIdeal s c D I J hs hD P ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hbase
  have hI0 : SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0 ≠ ⊥ := by
    intro hz
    apply hQ0
    rw [← SourceCurvePlaneImagePrime.contraction s c D I J hs hD P hdeg hP b hb hb0, hz]
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective
  have hlo : 1 ≤ (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hI0)
  exact le_antisymm ((plane_height_le s c D I J hs hD P hdeg hP b hb hb0).trans_eq hsource) hlo

end PaperP1.SourceCurveProjectionHeight
