module

public import PaperP1.Algebra.HomogeneousSplitRadicalData

/-! # The literal homogenized split-radical coordinate algebra is a domain -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalAlgebra

open Finset Polynomial PaperP1.FiniteQuadraticTower PaperP1.HomogeneousSplitRadicalData

local instance coefficientRing (F : Type*) [Field F] : CommRing (CoefficientField F) :=
  (inferInstance : Field (CoefficientField F)).toCommRing

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing (CoefficientField F)[X][X] := inferInstance

abbrev GenericBase (F : Type*) [Field F] := FiniteRootWordSquares.FunctionField (CoefficientField F)

def genericMap (F : Type*) [Field F] : PolynomialRing F →+* GenericBase F :=
  (algebraMap (CoefficientField F)[X][X] (GenericBase F)).comp (baseMap F)

def radicands {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (e : ι → ℕ) (I J : ι → Finset ℤ) :
    List (PolynomialRing F) := l.map fun i ↦ radicand (c i) (e i) (I i) (J i)

abbrev CoordinateAlgebra {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (e : ι → ℕ) (I J : ι → Finset ℤ) :=
  Tower (PolynomialRing F) (radicands l c e I J)

theorem genericMap_injective (F : Type*) [Field F] : Function.Injective (genericMap F) :=
  (IsFractionRing.injective (CoefficientField F)[X][X] (GenericBase F)).comp (baseMap_injective F)

theorem generic_radicands {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (c : ι → F) (e : ι → ℕ) (I J : ι → Finset ℤ) :
    (radicands l c e I J).map (genericMap F) =
      l.map (fun i ↦ FiniteRootWordSquares.scaledFunction (scalar (c i) (e i)) (roots F (I i)) (roots F (J i))) := by
  simp only [radicands, List.map_map, Function.comp_def, genericMap, RingHom.comp_apply,
    radicand_map, FiniteRootWordSquares.scaledFunction]

theorem generic_field {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (e : ι → ℕ) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsField (Tower (GenericBase F) ((radicands l c e I J).map (genericMap F))) ∧
      Module.finrank (GenericBase F) (Tower (GenericBase F) ((radicands l c e I J).map (genericMap F))) = 2 ^ l.length := by
  rw [generic_radicands]
  apply FiniteRootWordField.source_field l hl (fun i ↦ scalar (c i) (e i))
    (fun i ↦ scalar_ne_zero (c i) (hc i) (e i)) (fun i ↦ roots F (I i)) (fun i ↦ roots F (J i))
  · intro i
    rcases hne i with hi | hj
    · exact Or.inl (roots_nonempty F (I i) hi)
    · exact Or.inr (roots_nonempty F (J i) hj)
  · intro i j hij
    exact roots_disjoint F _ _ (hI hij)
  · intro i j hij
    exact roots_disjoint F _ _ (hJ hij)

theorem coordinate_isDomain {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (e : ι → ℕ) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsDomain (CoordinateAlgebra l c e I J) :=
  QuadraticTowerBaseChange.source_isDomain (genericMap F) (genericMap_injective F) (radicands l c e I J)
    (generic_field l hl c hc e I J hne hI hJ).1.isDomain

theorem coordinate_finrank {F ι : Type*} [Field F]
    (l : List ι) (c : ι → F) (e : ι → ℕ) (I J : ι → Finset ℤ) :
    Module.finrank (PolynomialRing F) (CoordinateAlgebra l c e I J) = 2 ^ l.length := by
  simpa only [CoordinateAlgebra, radicands, List.length_map] using finrank (PolynomialRing F) (radicands l c e I J)

end PaperP1.HomogeneousSplitRadicalAlgebra
