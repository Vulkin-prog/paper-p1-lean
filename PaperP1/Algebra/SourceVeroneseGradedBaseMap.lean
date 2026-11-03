module

public import PaperP1.Algebra.SourceVeroneseGrading
public import PaperP1.Algebra.HomogeneousSplitRadicalBaseInjection
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! # The actual finite faithful standard-base map preserves the rescaled degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseGradedBaseMap

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalBaseInjection
  PaperP1.SourceVeroneseGrading

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

theorem rename_base_homogeneous (F ι : Type*) [Field F] (D m : ℕ)
    (p : MvPolynomial (Fin 3) F) (hp : p.IsHomogeneous m) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D) (MvPolynomial.rename Sum.inl p) m := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using MvPolynomial.isWeightedHomogeneous_zero F (weight ι D) m
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    rw [MvPolynomial.rename_monomial]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [SplitWeightedDegreeGenerators.pure_weight D _ (SplitBaseVeronese.mapDomain_base_pure d),
      Finsupp.degree_mapDomain, Finsupp.degree_eq_weight_one]
    exact hd

theorem basePolynomialMap_mem {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (m : ℕ)
    (p : MvPolynomial (Fin 3) F) (hp : p.IsHomogeneous m) :
    basePolynomialMap c D I J p ∈ HomogeneousSplitRadicalGrading.piece c D I J m :=
  Submodule.mem_map.mpr ⟨MvPolynomial.rename Sum.inl p, rename_base_homogeneous F ι D m p hp, rfl⟩

theorem standardBaseMap_mem {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (n : ℕ) (p : StandardBaseVeronese.nativeVeronese F D) (hp : p ∈ nativePiece F D n) :
    standardBaseMap s c D hD I J hs p ∈ sourcePiece c D I J n := by
  change (p : MvPolynomial (Fin 3) F).IsHomogeneous (n * D) at hp
  change basePolynomialMap c D I J (p : MvPolynomial (Fin 3) F) ∈ HomogeneousSplitRadicalGrading.piece c D I J (n * D)
  exact basePolynomialMap_mem c D I J (n * D) p hp

def gradedBaseMap {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    nativePiece F D →+*ᵍ sourcePiece c D I J where
  toRingHom := standardBaseMap s c D hD I J hs
  map_mem := fun {n} {p} hp ↦ standardBaseMap_mem s c D hD I J hs n p hp

theorem gradedBaseMap_injective {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Function.Injective (gradedBaseMap s c D hD I J hs) := standardBaseMap_injective s c D hD I J hs

theorem gradedBaseMap_finite {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) : (gradedBaseMap s c D hD I J hs).toRingHom.Finite :=
  standardBaseMap_finite s c D hD I J hs hdeg

end PaperP1.SourceVeroneseGradedBaseMap
