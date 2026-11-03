module

public import PaperP1.Algebra.HomogeneousSplitRadicalFiniteVeronese
public import PaperP1.Algebra.StandardBaseVeronese

/-! # The standard plane Veronese algebra maps faithfully and finitely into the actual source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalBaseInjection

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalPresentation
  PaperP1.HomogeneousSplitRadicalFiniteVeronese PaperP1.TrivariatePolynomialEquiv

local instance baseRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

def basePolynomialMap {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    MvPolynomial (Fin 3) F →ₐ[F] CoordinateRing c D I J :=
  (quotientMap c D I J).comp (MvPolynomial.rename Sum.inl)

theorem presentationEquiv_base {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (p : MvPolynomial (Fin 3) F) :
    presentationEquiv s c D I J hs (basePolynomialMap c D I J p) =
      algebraMap (PolynomialRing F) (FiniteQuadraticTower.Tower (PolynomialRing F) s) (threeEquiv F p) := by
  change QuadraticTowerPresentation.evaluation (PolynomialRing F) s
    (polynomialEquiv F s.length (MvPolynomial.rename Sum.inl p)) = _
  rw [polynomialEquiv_rename]
  exact MvPolynomial.aeval_C _ _

theorem basePolynomialMap_injective {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Function.Injective (basePolynomialMap c D I J) := by
  intro p q hpq
  apply (threeEquiv F).injective
  apply FiniteQuadraticTower.base_injective (PolynomialRing F) s
  have hh := congrArg (presentationEquiv s c D I J hs) hpq
  simpa only [presentationEquiv_base] using hh

def baseEquiv {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    StandardBaseVeronese.nativeVeronese F D ≃ₐ[F] base c D I J := by
  let e₁ : StandardBaseVeronese.nativeVeronese F D ≃ₐ[F]
      (StandardBaseVeronese.nativeVeronese F D).map (basePolynomialMap c D I J) :=
    Subalgebra.equivMapOfInjective _ _ (basePolynomialMap_injective s c D I J hs)
  let e₂ : (StandardBaseVeronese.nativeVeronese F D).map (basePolynomialMap c D I J) ≃ₐ[F]
      base c D I J :=
    Subalgebra.equivOfEq _ _ (StandardBaseVeronese.baseAlgebra_eq_map D hD (quotientMap c D I J)).symm
  exact e₁.trans e₂

theorem baseEquiv_apply {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (p : StandardBaseVeronese.nativeVeronese F D) :
    (baseEquiv s c D hD I J hs p : CoordinateRing c D I J) = basePolynomialMap c D I J p := rfl

def standardBaseMap {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    StandardBaseVeronese.nativeVeronese F D →+* HomogeneousSplitRadicalVeronese.veronese c D I J :=
  (baseMap c D I J).comp (baseEquiv s c D hD I J hs).toRingHom

theorem standardBaseMap_injective {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Function.Injective (standardBaseMap s c D hD I J hs) := by
  intro p q hpq
  apply (baseEquiv s c D hD I J hs).injective
  apply Subtype.ext
  exact congrArg (fun x : HomogeneousSplitRadicalVeronese.veronese c D I J ↦
    (x : CoordinateRing c D I J)) hpq

theorem standardBaseMap_finite {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) : (standardBaseMap s c D hD I J hs).Finite := by
  exact (baseMap_finite c D hD I J hdeg).comp
    (RingHom.Finite.of_surjective (baseEquiv s c D hD I J hs).toRingHom (baseEquiv s c D hD I J hs).surjective)

end PaperP1.HomogeneousSplitRadicalBaseInjection
