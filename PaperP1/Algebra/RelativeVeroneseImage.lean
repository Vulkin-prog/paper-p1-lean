module

public import PaperP1.Algebra.RelativeVeroneseMap

/-! # The actual relative quadratic image is exactly the source Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeVeroneseImage

open Polynomial PaperP1.FiniteQuadraticTower PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalGrading PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalFiniteVeronese PaperP1.HomogeneousSplitRadicalBaseInjection
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.RelativeVeroneseMap

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

theorem scalar_range
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D) :
    Set.range (algebraMap (Base F D) (CoordinateRing c D I J)) = (base c D I J : Set (CoordinateRing c D I J)) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    change basePolynomialMap c D I J (r : MvPolynomial (Fin 3) F) ∈ base c D I J
    simpa only [baseEquiv_apply] using (baseEquiv s c D hD I J hs r).property
  · intro hx
    let b : base c D I J := ⟨x, hx⟩
    let r := (baseEquiv s c D hD I J hs).symm b
    refine ⟨r, ?_⟩
    change basePolynomialMap c D I J (r : MvPolynomial (Fin 3) F) = x
    have he := congrArg (fun y : base c D I J ↦ (y : CoordinateRing c D I J))
      ((baseEquiv s c D hD I J hs).apply_symm_apply b)
    simpa only [baseEquiv_apply] using he

theorem roots_range
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Set.range (fun j ↦ toAlg s c D I J hdeg hs (root (Base F D) (RelativeVeroneseMap.radicands s c D I J hdeg) j)) =
      Set.range (fun i : Fin s.length ↦ quotientMap c D I J (MvPolynomial.X (Sum.inr i))) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨indexEquiv s c D I J hdeg j, (toQuotient_root s c D I J hdeg hs j).symm⟩
  · rintro ⟨i, rfl⟩
    let j := (indexEquiv s c D I J hdeg).symm i
    refine ⟨j, ?_⟩
    change toQuotient s c D I J hdeg hs
      (root (Base F D) (RelativeVeroneseMap.radicands s c D I J hdeg) j) = _
    rw [toQuotient_root]
    change quotientMap c D I J (MvPolynomial.X (Sum.inr
      ((indexEquiv s c D I J hdeg) ((indexEquiv s c D I J hdeg).symm i)))) = _
    rw [Equiv.apply_symm_apply]

def imageF
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Subalgebra F (CoordinateRing c D I J) := ((toAlg s c D I J hdeg hs).range).restrictScalars F

theorem image_eq_source
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D) :
    imageF s c D I J hdeg hs = HomogeneousSplitRadicalVeronese.veronese c D I J := by
  rw [imageF, QuadraticTowerImageBasis.image_eq_adjoin,
    Algebra.adjoin_eq_adjoin_union F (Set.univ : Set (Base F D)) _ (by simp),
    Set.image_univ, scalar_range s c D I J hs hD, roots_range]
  exact (relative_generators c D hD I J).symm

end PaperP1.RelativeVeroneseImage
