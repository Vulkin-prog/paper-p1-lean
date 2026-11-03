module

public import PaperP1.Algebra.RelativeVeroneseImage

/-! # The actual source Veronese algebra is finite free of rank 2^k over the standard base -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeVeroneseBasis

open Module Polynomial PaperP1.FiniteQuadraticTower PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalGrading PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalBaseInjection PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.RelativeVeroneseMap PaperP1.RelativeVeroneseImage

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

local instance coordinateAlgebra {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    Algebra (Base F D) (CoordinateRing c D I J) := (scalarMap c D I J).toAlgebra

local instance coordinateTower {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    IsScalarTower F (Base F D) (CoordinateRing c D I J) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap F (CoordinateRing c D I J) a =
    basePolynomialMap c D I J (algebraMap F (MvPolynomial (Fin 3) F) a)
  exact ((basePolynomialMap c D I J).commutes a).symm

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

def sourceBasis
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D) :
    letI : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
      (standardBaseMap s c D hD I J hs).toAlgebra
    Basis (Index (RelativeVeroneseMap.radicands s c D I J hdeg)) (Base F D)
      (HomogeneousSplitRadicalVeronese.veronese c D I J) := by
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (standardBaseMap s c D hD I J hs).toAlgebra
  let eF : imageF s c D I J hdeg hs ≃ₐ[F] HomogeneousSplitRadicalVeronese.veronese c D I J :=
    Subalgebra.equivOfEq _ _ (image_eq_source s c D I J hdeg hs hD)
  let eRing : (toAlg s c D I J hdeg hs).range ≃+* HomogeneousSplitRadicalVeronese.veronese c D I J :=
    eF.toRingEquiv
  let e : (toAlg s c D I J hdeg hs).range ≃ₐ[Base F D] HomogeneousSplitRadicalVeronese.veronese c D I J :=
    { eRing with commutes' := by intro r; apply Subtype.ext; rfl }
  exact (QuadraticTowerImageBasis.imageBasis (RelativeVeroneseMap.radicands s c D I J hdeg)
    (toAlg s c D I J hdeg hs) (toQuotient_injective s c D I J hdeg hs)).map e.toLinearEquiv

include hdeg in
theorem source_free_rank
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D) :
    letI : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
      (standardBaseMap s c D hD I J hs).toAlgebra
    Module.Free (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) ∧
      Module.Finite (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) ∧
      Module.finrank (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) = 2 ^ s.length := by
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (standardBaseMap s c D hD I J hs).toAlgebra
  let b := sourceBasis s c D I J hdeg hs hD
  refine ⟨Module.Free.of_basis b, Module.Finite.of_basis b, ?_⟩
  rw [Module.finrank_eq_card_basis b, index_card, radicands_length]

theorem sourceBasis_apply
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
    (i : Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    ((sourceBasis s c D I J hdeg hs hD i : HomogeneousSplitRadicalVeronese.veronese c D I J) : CoordinateRing c D I J) =
      toQuotient s c D I J hdeg hs (basis (Base F D) (RelativeVeroneseMap.radicands s c D I J hdeg) i) := by
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (standardBaseMap s c D hD I J hs).toAlgebra
  rw [sourceBasis, Basis.map_apply]
  exact QuadraticTowerImageBasis.imageBasis_apply (RelativeVeroneseMap.radicands s c D I J hdeg)
    (toAlg s c D I J hdeg hs) (toQuotient_injective s c D I J hdeg hs) i

end PaperP1.RelativeVeroneseBasis
