module

public import PaperP1.Geometry.SourceProjectiveFlat
public import PaperP1.Geometry.ProjRadicalRank

/-! # The actual projective cover is finite flat, surjective and of constant rank 2^k -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveRank

open AlgebraicGeometry HomogeneousLocalization Module PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap PaperP1.SourceVeroneseIrrelevant
  PaperP1.FiniteQuadraticTower

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type u) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type u) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

variable {F : Type u} [Field F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

set_option backward.isDefEq.respectTransparency false in
theorem map_rank (x : SourceProjectiveMap.baseScheme.{u} F D hD) :
    (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg).finrank x = 2 ^ s.length := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  have : Flat (ProjRadicalMap.map (gradedBaseMap s c D hD I J hs)
      (source_irrelevant_le_radical s c D hD I J hs hdeg)) := by
    simpa only [SourceProjectiveMap.map] using SourceProjectiveFlat.map_flat s c D hD I J hs hdeg
  have : IsFinite (ProjRadicalMap.map (gradedBaseMap s c D hD I J hs)
      (source_irrelevant_le_radical s c D hD I J hs hdeg)) := by
    simpa only [SourceProjectiveMap.map] using SourceProjectiveFinite.map_isFinite s c D hD I J hs hdeg
  have hcover := Proj.iSup_basicOpen_eq_top (nativePiece F D)
    (fun b : nativePiece F D 1 ↦ (b : Base F D)) (SourceProjectiveFlat.native_degree_one_cover F D hD)
  have hx : x ∈ ⨆ b : nativePiece F D 1, Proj.basicOpen (nativePiece F D) (b : Base F D) := by
    rw [hcover]
    trivial
  obtain ⟨b, hbx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hb0 : (b : Base F D) ≠ 0 := by
    intro hzero
    simp only [hzero, Proj.basicOpen_zero, TopologicalSpace.Opens.mem_bot] at hbx
  have : IsDomain (Away (nativePiece F D) (b : Base F D)) :=
    GradedChartBasis.chart_isDomain (nativePiece F D) hb0
  have hrange : x ∈ (Proj.awayι (nativePiece F D) (b : Base F D) b.property
      (by decide : 0 < 1)).opensRange := by
    rwa [Proj.opensRange_awayι]
  change ∃ p, Proj.awayι (nativePiece F D) (b : Base F D) b.property (by decide : 0 < 1) p = x at hrange
  obtain ⟨p, hp⟩ := hrange
  have hr := ProjRadicalRank.rank_on_chart (gradedBaseMap s c D hD I J hs)
    (source_irrelevant_le_radical s c D hD I J hs hdeg) b.property
    (SourceVeroneseChartBasis.chartBasis s c D I J hdeg hs hD b b.property) p
  rw [hp] at hr
  simpa only [SourceProjectiveMap.map, index_card, RelativeVeroneseMap.radicands_length] using hr

theorem map_surjective : Surjective (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg) := by
  have : Flat (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg) :=
    SourceProjectiveFlat.map_flat s c D hD I J hs hdeg
  have : IsFinite (SourceProjectiveMap.map.{u} s c D hD I J hs hdeg) :=
    SourceProjectiveFinite.map_isFinite s c D hD I J hs hdeg
  apply (Scheme.Hom.one_le_finrank_iff_surjective _).mp
  intro x
  rw [map_rank]
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

end PaperP1.SourceProjectiveRank
