module

public import PaperP1.Geometry.SourceProjectiveFinite
public import PaperP1.Geometry.ProjRadicalFlat
public import PaperP1.Algebra.SourceVeroneseChartBasis

/-! # The actual finite projective source morphism is flat -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveFlat

open AlgebraicGeometry HomogeneousLocalization PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

theorem native_degree_one_cover (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := nativeGrading F D hD
    (HomogeneousIdeal.irrelevant (nativePiece F D)).toIdeal ≤
      Ideal.span (Set.range fun b : nativePiece F D 1 ↦ (b : Base F D)) := by
  let := nativeGrading F D hD
  rw [IrrelevantGenerated.irrelevant_eq_span (nativePiece F D)
    (nativePiece F D 1 : Set (Base F D)) (fun _ hb ↦ hb) (native_generated_degree_one F D hD)]
  apply Ideal.span_mono
  intro b hb
  exact ⟨⟨b, hb⟩, rfl⟩

theorem chart_map_flat {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (b : Base F D) (hb : b ∈ nativePiece F D 1) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    (Away.map (gradedBaseMap s c D hD I J hs) b).Flat := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let : Algebra (Away (nativePiece F D) b)
      (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
    (Away.map (gradedBaseMap s c D hD I J hs) b).toAlgebra
  have : Module.Free (Away (nativePiece F D) b)
      (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
    .of_basis (SourceVeroneseChartBasis.chartBasis s c D I J hdeg hs hD b hb)
  change Module.Flat (Away (nativePiece F D) b)
    (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b))
  infer_instance

theorem map_flat {F : Type u} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    Flat (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact ProjRadicalFlat.map_flat (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg) (native_degree_one_cover F D hD)
    (fun b ↦ chart_map_flat s c D hD I J hs hdeg b b.property)

end PaperP1.SourceProjectiveFlat
