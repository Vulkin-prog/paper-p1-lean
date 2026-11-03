module

public import PaperP1.Geometry.SourceProjectiveMap
public import PaperP1.Geometry.ProjIntegral
public import PaperP1.Algebra.StandardVeroneseCoordinates

/-! # The actual projective base and source are integral under the source independence hypotheses -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveIntegral

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap
  PaperP1.StandardVeroneseCoordinates

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

theorem base_irrelevant_ne_bot (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := nativeGrading F D hD
    (HomogeneousIdeal.irrelevant (nativePiece F D)).toIdeal ≠ ⊥ := by
  let := nativeGrading F D hD
  exact ProjIntegral.irrelevant_ne_bot_of_homogeneous (nativePiece F D) (by decide : 0 < 1)
    (coordinatePower_mem F D 2) (coordinatePower_ne_zero F D 2)

theorem base_integral (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    IsIntegral (SourceProjectiveMap.baseScheme.{u} F D hD) := by
  let := nativeGrading F D hD
  exact ProjIntegral.integral (nativePiece F D) (base_irrelevant_ne_bot F D hD)

theorem source_irrelevant_ne_bot {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    (HomogeneousIdeal.irrelevant (sourcePiece c D I J)).toIdeal ≠ ⊥ := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  have hnz : gradedBaseMap s c D hD I J hs (coordinatePower F D 2) ≠ 0 := by
    intro hz
    apply coordinatePower_ne_zero F D 2
    apply gradedBaseMap_injective s c D hD I J hs
    exact hz.trans (map_zero (gradedBaseMap s c D hD I J hs)).symm
  exact ProjIntegral.irrelevant_ne_bot_of_homogeneous (sourcePiece c D I J) (by decide : 0 < 1)
    ((gradedBaseMap s c D hD I J hs).map_mem (coordinatePower_mem F D 2)) hnz

theorem source_integral {F : Type u} [Field F] [CharZero F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsIntegral (SourceProjectiveMap.sourceScheme.{u} c D I J hdeg hD) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  have := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  exact ProjIntegral.integral (sourcePiece c D I J)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg)

end PaperP1.SourceProjectiveIntegral
