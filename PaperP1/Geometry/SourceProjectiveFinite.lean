module

public import PaperP1.Geometry.SourceProjectiveMap
public import PaperP1.Geometry.ProjRadicalCharts

/-! # Finiteness of the actual source projective morphism -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveFinite

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

theorem chart_map_finite {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (b : Base F D) (hb : b ∈ nativePiece F D 1) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    (HomogeneousLocalization.Away.map (gradedBaseMap s c D hD I J hs) b).Finite := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact GradedDehomogenization.away_map_finite (nativePiece F D) hb
    (gradedBaseMap s c D hD I J hs) (gradedBaseMap_finite s c D hD I J hs hdeg)

theorem map_isFinite {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    IsFinite (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  apply ProjRadicalCharts.map_finite (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg)
  · rw [IrrelevantGenerated.irrelevant_eq_span (nativePiece F D)
      (nativePiece F D 1 : Set (Base F D)) (fun _ hb ↦ hb)
      (native_generated_degree_one F D hD)]
    apply Ideal.span_mono
    intro b hb
    exact ⟨⟨b, hb⟩, rfl⟩
  · exact gradedBaseMap_finite s c D hD I J hs hdeg

end PaperP1.SourceProjectiveFinite
