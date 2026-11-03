module

public import PaperP1.Algebra.GradedChartBasis
public import PaperP1.Algebra.SourceVeroneseHomogeneousBasis
public import PaperP1.Algebra.SourceVeroneseGradedBaseMap

/-! # The actual affine chart maps are free of rank 2^k -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseChartBasis

open HomogeneousLocalization Module PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap
  PaperP1.RelativeVeroneseBasis PaperP1.FiniteQuadraticTower PaperP1.QuadraticTowerHomogeneousBasis

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (b : Base F D) (hb : b ∈ nativePiece F D 1)

def chartBasis :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI : Algebra (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
      (Away.map (gradedBaseMap s c D hD I J hs) b).toAlgebra
    Basis (Index (RelativeVeroneseMap.radicands s c D I J hdeg)) (Away (nativePiece F D) b)
      (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact GradedChartBasis.basis (nativePiece F D) hb (gradedBaseMap s c D hD I J hs)
    (sourceBasis s c D I J hdeg hs hD)

set_option maxRecDepth 2048 in
theorem chartBasis_apply (i : Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI : Algebra (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
      (Away.map (gradedBaseMap s c D hD I J hs) b).toAlgebra
    chartBasis s c D I J hdeg hs hD b hb i =
      GradedDehomogenization.map (sourcePiece c D I J)
        ((gradedBaseMap s c D hD I J hs).map_mem hb) (sourceBasis s c D I J hdeg hs hD i) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact GradedChartBasis.basis_apply (nativePiece F D) hb (gradedBaseMap s c D hD I J hs)
    (sourceBasis s c D I J hdeg hs hD) i

theorem chartBasis_fraction (i : Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI : Algebra (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
      (Away.map (gradedBaseMap s c D hD I J hs) b).toAlgebra
    chartBasis s c D I J hdeg hs hD b hb i =
      Away.mk (sourcePiece c D I J) ((gradedBaseMap s c D hD I J hs).map_mem hb)
        (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i)
        (sourceBasis s c D I J hdeg hs hD i)
        (by simpa only [smul_eq_mul, mul_one] using
          SourceVeroneseHomogeneousBasis.sourceBasis_mem s c D I J hdeg hs hD i) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  rw [chartBasis_apply, GradedDehomogenization.map_homogeneous (sourcePiece c D I J) _ _ _
    (SourceVeroneseHomogeneousBasis.sourceBasis_mem s c D I J hdeg hs hD i)]

include hb in
theorem chart_free_rank (hb0 : b ≠ 0) :
    letI := nativeGrading F D hD
    letI := sourceGrading c D I J hdeg hD
    letI : Algebra (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
      (Away.map (gradedBaseMap s c D hD I J hs) b).toAlgebra
    Module.Free (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) ∧
      Module.Finite (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) ∧
      Module.finrank (Away (nativePiece F D) b)
        (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) = 2 ^ s.length := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let : Algebra (Away (nativePiece F D) b)
      (Away (sourcePiece c D I J) (gradedBaseMap s c D hD I J hs b)) :=
    (Away.map (gradedBaseMap s c D hD I J hs) b).toAlgebra
  have := GradedChartBasis.chart_isDomain (nativePiece F D) hb0
  let e := chartBasis s c D I J hdeg hs hD b hb
  refine ⟨.of_basis e, .of_basis e, ?_⟩
  rw [Module.finrank_eq_card_basis e, index_card, RelativeVeroneseMap.radicands_length]

end PaperP1.SourceVeroneseChartBasis
