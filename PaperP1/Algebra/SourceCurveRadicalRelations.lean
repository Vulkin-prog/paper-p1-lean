module

public import PaperP1.Algebra.SourceCurveQuotient

/-! # Literal homogeneous radical equations in the actual source curve quotients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveRadicalRelations

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.HomogeneousSplitRadicalGrading

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
  SourceCurveQuotient.sourceQuotientSemiring s c D I J P
local instance baseQuotientSemiring : Semiring (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientSemiring s c D I J hs hD P

def root (i : Fin s.length) : SourceCurveQuotient.SourceRing s c D I J P :=
  Ideal.Quotient.mk P (HomogeneousSplitRadicalFiniteVeronese.radical c D I J i)

def baseRadicand (i : Fin s.length) : SourceCurveQuotient.BaseRing s c D I J hs hD P :=
  Ideal.Quotient.mk (SourceCurveQuotient.baseIdeal s c D I J hs hD P)
    (HomogeneousSplitRadicalVeroneseTowerData.baseRadicand (c i) D (I i) (J i) (hdeg i))

theorem root_mem_one (i : Fin s.length) : root s c D I J P i ∈ SourceCurveQuotient.sourcePiece s c D I J P 1 :=
  Submodule.mem_map.mpr ⟨_, SourceVeroneseGrading.source_radical_mem_one c D I J i, rfl⟩

theorem baseRadicand_mem_two (i : Fin s.length) : baseRadicand s c D I J hs hD P hdeg i ∈
    SourceCurveQuotient.basePiece s c D I J hs hD P 2 := by
  apply Submodule.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  change (HomogeneousSplitRadicalPolynomials.nativeRadicand (c i)
    (2 * D - ((I i).card + (J i).card)) (I i) (J i)).IsHomogeneous (2 * D)
  have hi := hdeg i
  convert HomogeneousSplitRadicalPolynomials.nativeRadicand_homogeneous
    (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i) using 1; omega

include hdeg in
theorem original_square (i : Fin s.length) :
    HomogeneousSplitRadicalFiniteVeronese.radical c D I J i ^ 2 =
      SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs
        (HomogeneousSplitRadicalVeroneseTowerData.baseRadicand (c i) D (I i) (J i) (hdeg i)) := by
  apply Subtype.ext
  change (HomogeneousSplitRadicalFiniteVeronese.radical c D I J i : CoordinateRing c D I J) ^ 2 =
    HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J
      (HomogeneousSplitRadicalVeroneseTowerData.baseRadicand (c i) D (I i) (J i) (hdeg i) : MvPolynomial (Fin 3) F)
  exact HomogeneousSplitRadicalFiniteVeronese.radical_square c D I J i

theorem root_square (i : Fin s.length) : root s c D I J P i ^ 2 =
    SourceCurveQuotient.map s c D I J hs hD P (baseRadicand s c D I J hs hD P hdeg i) := by
  change Ideal.Quotient.mk P (HomogeneousSplitRadicalFiniteVeronese.radical c D I J i) ^ 2 =
    Ideal.Quotient.mk P (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs
      (HomogeneousSplitRadicalVeroneseTowerData.baseRadicand (c i) D (I i) (J i) (hdeg i)))
  rw [← map_pow, original_square s c D I J hs hD hdeg]

end PaperP1.SourceCurveRadicalRelations
