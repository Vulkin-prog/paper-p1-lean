module

public import PaperP1.Algebra.SourceVeroneseVectorBasis
public import PaperP1.Algebra.WeightedVeronesePieceIndex
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # The exact eventual Hilbert function of the actual source Veronese -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseHilbert

open Module PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.QuadraticTowerHomogeneousBasis PaperP1.FiniteQuadraticTower

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)

include hdeg hs hD

theorem piece_finite_all (n : ℕ) :
    Module.Finite F (SourceVeroneseGrading.sourcePiece c D I J n) := by
  have : Finite (WeightedVeronesePieceIndex.PieceIndex D
      (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg)) n) :=
    WeightedVeronesePieceIndex.piece_finite_all D _ n
  let : Fintype (WeightedVeronesePieceIndex.PieceIndex D
      (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg)) n) := Fintype.ofFinite _
  exact Module.Finite.of_basis (SourceVeroneseVectorBasis.pieceBasis s c D I J hdeg hs hD n)

theorem piece_finrank_all (n : ℕ) :
    Module.finrank F (SourceVeroneseGrading.sourcePiece c D I J n) =
      ∑ j : {j : Index (RelativeVeroneseMap.radicands s c D I J hdeg) //
          indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) j ≤ n},
        ((n - indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) j.1) * D + 2).choose 2 := by
  classical
  rw [Module.finrank_eq_nat_card_basis (SourceVeroneseVectorBasis.pieceBasis s c D I J hdeg hs hD n)]
  exact WeightedVeronesePieceIndex.piece_card_all D _ n

theorem piece_finite (n : ℕ) (hn : s.length ≤ n) :
    Module.Finite F (SourceVeroneseGrading.sourcePiece c D I J n) := by
  have hi : Finite (WeightedVeronesePieceIndex.PieceIndex D
      (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg)) n) :=
    WeightedVeronesePieceIndex.piece_finite D _ n (fun j ↦
      (SourceVeroneseHomogeneousBasis.sourceBasis_degree_bound s c D I J hdeg j).trans hn)
  let : Fintype (WeightedVeronesePieceIndex.PieceIndex D
      (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg)) n) := Fintype.ofFinite _
  exact Module.Finite.of_basis (SourceVeroneseVectorBasis.pieceBasis s c D I J hdeg hs hD n)

theorem piece_finrank (n : ℕ) (hn : s.length ≤ n) :
    Module.finrank F (SourceVeroneseGrading.sourcePiece c D I J n) =
      ∑ j : Index (RelativeVeroneseMap.radicands s c D I J hdeg),
        ((n - indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) j) * D + 2).choose 2 := by
  rw [Module.finrank_eq_nat_card_basis (SourceVeroneseVectorBasis.pieceBasis s c D I J hdeg hs hD n)]
  exact WeightedVeronesePieceIndex.piece_card D _ n (fun j ↦
    (SourceVeroneseHomogeneousBasis.sourceBasis_degree_bound s c D I J hdeg j).trans hn)

end PaperP1.SourceVeroneseHilbert
