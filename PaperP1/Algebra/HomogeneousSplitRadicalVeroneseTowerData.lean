module

public import PaperP1.Algebra.HomogeneousSplitRadicalBaseInjection
public import PaperP1.Algebra.QuadraticTowerGeneratorBaseChange
public import PaperP1.Algebra.QuadraticTowerImageBasis

/-! # The actual homogenized radicands as elements of the standard base Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalVeroneseTowerData

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalPolynomials
  PaperP1.StandardBaseVeronese PaperP1.TrivariatePolynomialEquiv

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Base (F : Type*) [Field F] (D : ℕ) := nativeVeronese F D

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance

def polynomialMap (F : Type*) [Field F] (D : ℕ) : Base F D →+* PolynomialRing F :=
  (threeEquiv F).toRingHom.comp (nativeVeronese F D).val.toRingHom

theorem polynomialMap_injective (F : Type*) [Field F] (D : ℕ) : Function.Injective (polynomialMap F D) :=
  (threeEquiv F).injective.comp Subtype.val_injective

theorem radicand_mem {F : Type*} [Field F] (c : F) (D : ℕ) (I J : Finset ℤ)
    (hdeg : I.card + J.card ≤ 2 * D) :
    nativeRadicand c (2 * D - (I.card + J.card)) I J ∈ nativeVeronese F D := by
  apply GradedVeroneseAlgebra.piece_mem _ D 2
  change (nativeRadicand c (2 * D - (I.card + J.card)) I J).IsHomogeneous (2 * D)
  convert nativeRadicand_homogeneous c (2 * D - (I.card + J.card)) I J using 1; omega

def baseRadicand {F : Type*} [Field F] (c : F) (D : ℕ) (I J : Finset ℤ)
    (hdeg : I.card + J.card ≤ 2 * D) : Base F D :=
  ⟨nativeRadicand c (2 * D - (I.card + J.card)) I J, radicand_mem c D I J hdeg⟩

theorem baseRadicand_map {F : Type*} [Field F] (c : F) (D : ℕ) (I J : Finset ℤ)
    (hdeg : I.card + J.card ≤ 2 * D) :
    polynomialMap F D (baseRadicand c D I J hdeg) = radicand c (2 * D - (I.card + J.card)) I J :=
  nativeRadicand_map c _ I J

def baseRadicands {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (D : ℕ)
    (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) : List (Base F D) :=
  l.map fun i ↦ baseRadicand (c i) D (I i) (J i) (hdeg i)

theorem baseRadicands_map {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (D : ℕ)
    (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    (baseRadicands l c D I J hdeg).map (polynomialMap F D) =
      HomogeneousSplitRadicalAlgebra.radicands l c (fun i ↦ 2 * D - ((I i).card + (J i).card)) I J := by
  simp only [baseRadicands, HomogeneousSplitRadicalAlgebra.radicands, List.map_map, Function.comp_def,
    baseRadicand_map]

abbrev RelativeTower {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (D : ℕ)
    (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :=
  FiniteQuadraticTower.Tower (Base F D) (baseRadicands l c D I J hdeg)

theorem relative_finrank {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (D : ℕ)
    (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    Module.finrank (Base F D) (RelativeTower l c D I J hdeg) = 2 ^ l.length := by
  simpa only [RelativeTower, baseRadicands, List.length_map] using
    FiniteQuadraticTower.finrank (Base F D) (baseRadicands l c D I J hdeg)

theorem relative_map_injective {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (D : ℕ)
    (I J : ι → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    Function.Injective (QuadraticTowerBaseChange.mapData (polynomialMap F D) (baseRadicands l c D I J hdeg)).hom :=
  QuadraticTowerBaseChange.map_injective _ (polynomialMap_injective F D) _

end PaperP1.HomogeneousSplitRadicalVeroneseTowerData
