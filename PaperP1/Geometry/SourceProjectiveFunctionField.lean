module

public import PaperP1.Geometry.SourceProjectiveIntegral
public import PaperP1.Geometry.ProjFunctionFieldMap

/-! # Actual source scheme function fields and the map induced by the projective cover -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveFunctionField

open AlgebraicGeometry CategoryTheory TopologicalSpace PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant
  PaperP1.SourceProjectiveIntegral

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

def baseEquiv (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := nativeGrading F D hD
    letI := base_integral F D hD
    (SourceProjectiveMap.baseScheme.{u} F D hD).functionField ≃+*
      ProjFunctionField.degreeZeroField (nativePiece F D) := by
  let := nativeGrading F D hD
  let := base_integral F D hD
  exact ProjFunctionField.equiv (nativePiece F D) (base_irrelevant_ne_bot F D hD)

variable {F : Type u} [Field F] [CharZero F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))

def sourceEquiv :
    letI := sourceGrading c D I J hdeg hD
    letI := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    (SourceProjectiveMap.sourceScheme.{u} c D I J hdeg hD).functionField ≃+*
      ProjFunctionField.degreeZeroField (sourcePiece c D I J) := by
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  exact ProjFunctionField.equiv (sourcePiece c D I J)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg)

theorem genericPoint_map :
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    SourceProjectiveMap.map.{u} s c D hD I J hs hdeg
        (genericPoint (SourceProjectiveMap.sourceScheme.{u} c D I J hdeg hD)) =
      genericPoint (SourceProjectiveMap.baseScheme.{u} F D hD) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousSplitRadicalVeronese.source_isDomain s c D I J hs hc hne hI hJ
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  exact ProjFunctionFieldMap.genericPoint_map (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg) (base_irrelevant_ne_bot F D hD)
    (source_irrelevant_ne_bot s c D hD I J hs hdeg) (gradedBaseMap_injective s c D hD I J hs)

def map :
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    (SourceProjectiveMap.baseScheme.{u} F D hD).functionField →+*
      (SourceProjectiveMap.sourceScheme.{u} c D I J hdeg hD).functionField := by
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  let e := congrArg (fun p : SourceProjectiveMap.baseScheme.{u} F D hD ↦
    (SourceProjectiveMap.baseScheme.{u} F D hD).presheaf.stalk p)
    (genericPoint_map s c D hD I J hs hdeg hc hne hI hJ).symm
  exact (eqToHom e ≫ (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg).stalkMap
    (genericPoint (SourceProjectiveMap.sourceScheme.{u} c D I J hdeg hD))).hom

theorem map_injective :
    letI := base_integral F D hD
    letI := source_integral s c D hD I J hs hdeg hc hne hI hJ
    Function.Injective (map s c D hD I J hs hdeg hc hne hI hJ) := by
  let := base_integral F D hD
  let := source_integral s c D hD I J hs hdeg hc hne hI hJ
  exact (map s c D hD I J hs hdeg hc hne hI hJ).injective

end PaperP1.SourceProjectiveFunctionField
