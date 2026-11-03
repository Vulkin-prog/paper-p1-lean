module

public import PaperP1.Geometry.VeroneseHomogeneousPrime
public import PaperP1.Algebra.SourceCurveQuotient

/-! # The actual source curve base prime lifts to a homogeneous prime of the ordinary plane ring -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurvePlaneImagePrime

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
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

def point [P.IsPrime] :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    ProjectiveSpectrum (SourceVeroneseGrading.nativePiece F D) := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  refine {
    asHomogeneousIdeal := ⟨SourceCurveQuotient.baseIdeal s c D I J hs hD P,
      SourceCurveQuotient.baseIdeal_homogeneous s c D I J hs hD P hdeg hP⟩
    isPrime := ?_
    not_irrelevant_le := ?_ }
  · change (P.comap (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs).toRingHom).IsPrime
    infer_instance
  · intro h
    obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp hb
    have hi := HomogeneousIdeal.mem_irrelevant_of_mem (SourceVeroneseGrading.nativePiece F D)
      (by decide : 0 < 1) ha
    have hm : a ∈ SourceCurveQuotient.baseIdeal s c D I J hs hD P := h hi
    exact hb0 (he.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm))

def planePoint [P.IsPrime] : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) F) := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  exact (VeroneseHomogeneousPrime.pointEquiv (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD).symm
    (point s c D I J hs hD P hdeg hP b hb hb0)

def ideal [P.IsPrime] : Ideal (MvPolynomial (Fin 3) F) :=
  (planePoint s c D I J hs hD P hdeg hP b hb hb0).asHomogeneousIdeal.toIdeal

theorem ideal_prime [P.IsPrime] : (ideal s c D I J hs hD P hdeg hP b hb hb0).IsPrime :=
  (planePoint s c D I J hs hD P hdeg hP b hb hb0).isPrime

theorem ideal_homogeneous [P.IsPrime] :
    (ideal s c D I J hs hD P hdeg hP b hb hb0).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) F) :=
  (planePoint s c D I J hs hD P hdeg hP b hb hb0).asHomogeneousIdeal.isHomogeneous

theorem contraction [P.IsPrime] :
    (ideal s c D I J hs hD P hdeg hP b hb hb0).comap (StandardBaseVeronese.nativeVeronese F D).val.toRingHom =
      SourceCurveQuotient.baseIdeal s c D I J hs hD P := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  exact VeroneseHomogeneousPrime.comap_inverse (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD
    (point s c D I J hs hD P hdeg hP b hb hb0)

end PaperP1.SourceCurvePlaneImagePrime
