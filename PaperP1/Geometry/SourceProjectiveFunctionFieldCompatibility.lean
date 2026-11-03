module

public import PaperP1.Geometry.SourceProjectiveFunctionField
public import PaperP1.Geometry.ProjFunctionFieldCompatibility

/-! # The actual source scheme function-field map agrees with the homogeneous fraction map -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveFunctionFieldCompatibility

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant
  PaperP1.SourceProjectiveIntegral

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

variable {F : Type u} [Field F] [CharZero F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))

def degreeZeroMap :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    ProjFunctionField.degreeZeroField (nativePiece F D) →+*
      ProjFunctionField.degreeZeroField (sourcePiece c D I J) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  exact ProjFunctionFieldMap.degreeZeroMap (gradedBaseMap s c D hD I J hs)
    (gradedBaseMap_injective s c D hD I J hs)

theorem map_eq :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    SourceProjectiveFunctionField.map s c D hD I J hs hdeg hc hne hI hJ =
      ProjFunctionFieldMap.map (gradedBaseMap s c D hD I J hs)
        (source_irrelevant_le_radical s c D hD I J hs hdeg) (base_irrelevant_ne_bot F D hD)
        (source_irrelevant_ne_bot s c D hD I J hs hdeg) (gradedBaseMap_injective s c D hD I J hs) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  rfl

theorem equiv_comp_map :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    (SourceProjectiveFunctionField.sourceEquiv s c D hD I J hs hdeg hc hne hI hJ).toRingHom.comp
        (SourceProjectiveFunctionField.map s c D hD I J hs hdeg hc hne hI hJ) =
      (degreeZeroMap s c D hD I J hs hdeg hc hne hI hJ).comp
        (SourceProjectiveFunctionField.baseEquiv F D hD).toRingHom := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  rw [map_eq]
  exact ProjFunctionFieldCompatibility.equiv_comp_map (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg) (base_irrelevant_ne_bot F D hD)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg) (gradedBaseMap_injective s c D hD I J hs)

end PaperP1.SourceProjectiveFunctionFieldCompatibility
