module

public import PaperP1.Algebra.HomogeneousSplitRadicalVeroneseTowerData
public import PaperP1.Algebra.QuadraticTowerListCongr

/-! # The relative Veronese quadratic tower maps faithfully into the actual weighted quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeVeroneseMap

open Polynomial PaperP1.FiniteQuadraticTower PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalGrading PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalPresentation PaperP1.HomogeneousSplitRadicalFiniteVeronese
  PaperP1.HomogeneousSplitRadicalBaseInjection PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.TrivariatePolynomialEquiv

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

def scalarMap {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    Base F D →+* CoordinateRing c D I J :=
  (basePolynomialMap c D I J).toRingHom.comp (StandardBaseVeronese.nativeVeronese F D).val.toRingHom

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

def radicands : List (Base F D) := baseRadicands (List.finRange s.length) c D I J hdeg

theorem radicands_length : (radicands s c D I J hdeg).length = s.length := by
  simp only [radicands, baseRadicands, List.length_map, List.length_finRange]

theorem radicands_map
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    (radicands s c D I J hdeg).map (polynomialMap F D) = s := by
  rw [radicands, baseRadicands_map]
  calc
    HomogeneousSplitRadicalAlgebra.radicands (List.finRange s.length) c
        (fun i ↦ 2 * D - ((I i).card + (J i).card)) I J =
        List.ofFn (fun i ↦ radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) := List.ofFn_eq_map.symm
    _ = List.ofFn s.get := congrArg List.ofFn (funext (fun i ↦ (hs i).symm))
    _ = s := List.ofFn_get s

abbrev RelativeTower := Tower (Base F D) (radicands s c D I J hdeg)

def toTower
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    RelativeTower s c D I J hdeg →+* Tower (PolynomialRing F) s :=
  (QuadraticTowerListCongr.congr (PolynomialRing F) (radicands_map s c D I J hdeg hs)).toRingHom.comp
    (QuadraticTowerBaseChange.mapData (polynomialMap F D) (radicands s c D I J hdeg)).hom

theorem toTower_injective
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Function.Injective (toTower s c D I J hdeg hs) :=
  (QuadraticTowerListCongr.congr (PolynomialRing F) (radicands_map s c D I J hdeg hs)).injective.comp
    (relative_map_injective (List.finRange s.length) c D I J hdeg)

theorem toTower_base
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (r : Base F D) :
    toTower s c D I J hdeg hs (algebraMap (Base F D) (RelativeTower s c D I J hdeg) r) =
      algebraMap (PolynomialRing F) (Tower (PolynomialRing F) s) (polynomialMap F D r) := by
  change QuadraticTowerListCongr.congr (PolynomialRing F) (radicands_map s c D I J hdeg hs)
    ((QuadraticTowerBaseChange.mapData (polynomialMap F D) (radicands s c D I J hdeg)).hom
      (algebraMap (Base F D) (RelativeTower s c D I J hdeg) r)) = _
  rw [QuadraticTowerBaseChange.MapData.commutes, QuadraticTowerListCongr.congr_base]

def toQuotient
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    RelativeTower s c D I J hdeg →+* CoordinateRing c D I J :=
  (presentationEquiv s c D I J hs).symm.toRingHom.comp (toTower s c D I J hdeg hs)

theorem toQuotient_injective
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Function.Injective (toQuotient s c D I J hdeg hs) :=
  (presentationEquiv s c D I J hs).symm.injective.comp (toTower_injective s c D I J hdeg hs)

theorem toQuotient_base
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (r : Base F D) :
    toQuotient s c D I J hdeg hs (algebraMap (Base F D) (RelativeTower s c D I J hdeg) r) = scalarMap c D I J r := by
  apply (presentationEquiv s c D I J hs).injective
  change presentationEquiv s c D I J hs ((presentationEquiv s c D I J hs).symm
      (toTower s c D I J hdeg hs (algebraMap (Base F D) (RelativeTower s c D I J hdeg) r))) =
    presentationEquiv s c D I J hs (basePolynomialMap c D I J (r : MvPolynomial (Fin 3) F))
  rw [RingEquiv.apply_symm_apply, toTower_base, presentationEquiv_base]
  rfl

def toAlg
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    RelativeTower s c D I J hdeg →ₐ[Base F D] CoordinateRing c D I J where
  toRingHom := toQuotient s c D I J hdeg hs
  commutes' := toQuotient_base s c D I J hdeg hs

def indexEquiv : Fin (radicands s c D I J hdeg).length ≃ Fin s.length where
  toFun i := ⟨i.val, by simpa only [radicands_length] using i.isLt⟩
  invFun i := ⟨i.val, by simpa only [radicands_length] using i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem presentationEquiv_radical
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (i : Fin s.length) :
    presentationEquiv s c D I J hs (quotientMap c D I J (MvPolynomial.X (Sum.inr i))) = root (PolynomialRing F) s i := by
  change QuadraticTowerPresentation.evaluation (PolynomialRing F) s
    (polynomialEquiv F s.length (MvPolynomial.X (Sum.inr i))) = _
  rw [polynomialEquiv_radical_X]
  exact QuadraticTowerPresentation.evaluation_X _ _ i

theorem toQuotient_root
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (i : Fin (radicands s c D I J hdeg).length) :
    toQuotient s c D I J hdeg hs (root (Base F D) (radicands s c D I J hdeg) i) =
      quotientMap c D I J (MvPolynomial.X (Sum.inr (indexEquiv s c D I J hdeg i))) := by
  apply (presentationEquiv s c D I J hs).injective
  change presentationEquiv s c D I J hs ((presentationEquiv s c D I J hs).symm
      (toTower s c D I J hdeg hs (root (Base F D) (radicands s c D I J hdeg) i))) = _
  rw [RingEquiv.apply_symm_apply, presentationEquiv_radical]
  change QuadraticTowerListCongr.congr (PolynomialRing F) (radicands_map s c D I J hdeg hs)
    ((QuadraticTowerBaseChange.mapData (polynomialMap F D) (radicands s c D I J hdeg)).hom
      (root (Base F D) (radicands s c D I J hdeg) i)) = _
  rw [QuadraticTowerGeneratorBaseChange.map_root, QuadraticTowerListCongr.congr_root]
  rfl

end PaperP1.RelativeVeroneseMap
