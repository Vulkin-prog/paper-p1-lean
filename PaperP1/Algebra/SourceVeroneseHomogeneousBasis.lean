module

public import PaperP1.Algebra.SourceVeroneseGrading
public import PaperP1.Algebra.RelativeVeroneseBasis
public import PaperP1.Algebra.QuadraticTowerHomogeneousBasis

/-! # The actual source free basis is homogeneous with its explicit radical-count degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseHomogeneousBasis

open Module Polynomial PaperP1.FiniteQuadraticTower PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalGrading PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalBaseInjection PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.RelativeVeroneseMap PaperP1.RelativeVeroneseBasis PaperP1.QuadraticTowerHomogeneousBasis

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

theorem mapped_root_mem
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (i : Fin (RelativeVeroneseMap.radicands s c D I J hdeg).length) :
    toQuotient s c D I J hdeg hs (root (Base F D) (RelativeVeroneseMap.radicands s c D I J hdeg) i) ∈
      HomogeneousSplitRadicalGrading.piece c D I J D := by
  rw [toQuotient_root]
  exact Submodule.mem_map.mpr ⟨MvPolynomial.X (Sum.inr (indexEquiv s c D I J hdeg i)),
    radical_variable_homogeneous F (Fin s.length) D _, rfl⟩

theorem mapped_basis_mem
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (i : Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    toQuotient s c D I J hdeg hs (basis (Base F D) (RelativeVeroneseMap.radicands s c D I J hdeg) i) ∈
      HomogeneousSplitRadicalGrading.piece c D I J
        (D * indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i) := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  exact QuadraticTowerHomogeneousBasis.basis_mem (HomogeneousSplitRadicalGrading.piece c D I J) D
    (RelativeVeroneseMap.radicands s c D I J hdeg) (toQuotient s c D I J hdeg hs)
    (mapped_root_mem s c D I J hdeg hs) i

theorem sourceBasis_mem
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
    (i : Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    sourceBasis s c D I J hdeg hs hD i ∈ SourceVeroneseGrading.sourcePiece c D I J
      (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i) := by
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (standardBaseMap s c D hD I J hs).toAlgebra
  change ((sourceBasis s c D I J hdeg hs hD i : HomogeneousSplitRadicalVeronese.veronese c D I J) : CoordinateRing c D I J) ∈
    HomogeneousSplitRadicalGrading.piece c D I J (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i * D)
  rw [sourceBasis_apply, Nat.mul_comm]
  exact mapped_basis_mem s c D I J hdeg hs i

theorem sourceBasis_degree_bound (i : Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i ≤ s.length := by
  simpa only [radicands_length] using indexWeight_le_length (RelativeVeroneseMap.radicands s c D I J hdeg) i

end PaperP1.SourceVeroneseHomogeneousBasis
