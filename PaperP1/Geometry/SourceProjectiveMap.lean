module

public import PaperP1.Geometry.ProjRadicalMap
public import PaperP1.Algebra.SourceVeroneseIrrelevant

/-! # The actual graded base inclusion induces a morphism of the source projective schemes -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveMap

open AlgebraicGeometry CategoryTheory PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

def baseScheme (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) : Scheme.{u} := by
  let := nativeGrading F D hD
  exact Proj (nativePiece F D)

def sourceScheme {F : Type u} {ι : Type} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) : Scheme.{u} := by
  let := sourceGrading c D I J hdeg hD
  exact Proj (sourcePiece c D I J)

def map {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    sourceScheme.{u} c D I J hdeg hD ⟶ baseScheme.{u} F D hD := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact ProjRadicalMap.map (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg)

theorem map_preimage_basicOpen {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (b : Base F D) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    map.{u} s c D hD I J hs hdeg ⁻¹ᵁ ProjectiveSpectrum.basicOpen (nativePiece F D) b =
      ProjectiveSpectrum.basicOpen (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact ProjRadicalMap.map_preimage_basicOpen (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg) b

end PaperP1.SourceProjectiveMap
