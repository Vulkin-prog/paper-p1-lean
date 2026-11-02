module

public import PaperP1.Algebra.SubspaceKernelCut
public import PaperP1.Algebra.CurveCriticalFibres
public import PaperP1.Arithmetic.FormalWordEncoding
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The actual regular functional-square subspace and its dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveCoordinateCut

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.CurveCriticalFibres PaperP1.CurveWordMap PaperP1.CurveFunctionField
  PaperP1.FormalWordPolynomials

local instance : CommRing ℤ[X][X] := inferInstance
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : AddCommGroup Words := inferInstance
local instance (V : Submodule (ZMod 2) Words) : AddCommGroup V := inferInstance

abbrev BadData (P : ℤ[X][X]) :=
  ((badOffsets P) → ZMod 2) × ((badOffsets (Bivariate.swap P)) → ZMod 2)

def badCoordinates (P : ℤ[X][X]) : Words →ₗ[ZMod 2] BadData P where
  toFun w := (fun u ↦ w.1 u.val, fun v ↦ w.2 v.val)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

abbrev SquareSpace (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words) :=
  LinearMap.ker ((classMap C₀ hx hy).comp V.subtype)

abbrev RegularSpace (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words) :=
  LinearMap.ker (((badCoordinates C₀).comp V.subtype).comp (SquareSpace C₀ hx hy V).subtype)

def inclusion (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words) :
    RegularSpace C₀ hx hy V →ₗ[ZMod 2] Words :=
  V.subtype.comp ((SquareSpace C₀ hx hy V).subtype.comp (RegularSpace C₀ hx hy V).subtype)

theorem inclusion_injective (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words) :
    Function.Injective (inclusion C₀ hx hy V) :=
  V.subtype_injective.comp ((SquareSpace C₀ hx hy V).subtype_injective.comp
    (RegularSpace C₀ hx hy V).subtype_injective)

theorem literal_square (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words)
    (e : RegularSpace C₀ hx hy V) :
    IsSquare (specialize C₀ (wordOver ℤ (inclusion C₀ hx hy V e).1.support
      (inclusion C₀ hx hy V e).2.support)) := by
  have he : classMap C₀ hx hy (inclusion C₀ hx hy V e) = 0 := e.val.property
  rw [FormalWordEncoding.support_representation (inclusion C₀ hx hy V e), classMap_encode] at he
  exact (FieldSquareClasses.ofNonzero_zero_iff _ (word_ne_zero C₀ hx hy _ _)).mp he

theorem first_regular (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words)
    (e : RegularSpace C₀ hx hy V) (u : ℤ) (hu : u ∈ (inclusion C₀ hx hy V e).1.support) :
    u ∉ badOffsets C₀ := by
  intro hbad
  have hz := congrArg (fun d : BadData C₀ ↦ d.1 ⟨u, hbad⟩) (LinearMap.mem_ker.mp e.property)
  exact (Finsupp.mem_support_iff.mp hu) hz

theorem second_regular (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words)
    (e : RegularSpace C₀ hx hy V) (v : ℤ) (hv : v ∈ (inclusion C₀ hx hy V e).2.support) :
    v ∉ badOffsets (Bivariate.swap C₀) := by
  intro hbad
  have hz := congrArg (fun d : BadData C₀ ↦ d.2 ⟨v, hbad⟩) (LinearMap.mem_ker.mp e.property)
  exact (Finsupp.mem_support_iff.mp hv) hz

theorem badData_finrank (P : ℤ[X][X]) :
    Module.finrank (ZMod 2) (BadData P) = (badOffsets P).card + (badOffsets (Bivariate.swap P)).card := by
  simp only [BadData, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem dimension_lower (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words)
    [Module.Finite (ZMod 2) V]
    (hrank : Module.finrank (ZMod 2) (V.map (classMap C₀ hx hy)) ≤ 1) :
    Module.finrank (ZMod 2) V - 1 - 6 * totalDegree C₀ ^ 2 ≤
      Module.finrank (ZMod 2) (RegularSpace C₀ hx hy V) := by
  have hrange : Module.finrank (ZMod 2) (LinearMap.range ((classMap C₀ hx hy).comp V.subtype)) ≤ 1 := by
    have he : LinearMap.range ((classMap C₀ hx hy).comp V.subtype) = V.map (classMap C₀ hx hy) := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w.val, w.property, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨w, hw⟩, rfl⟩
    rw [he]
    exact hrank
  have hfirst := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (V := V)
    (V₂ := FieldSquareClasses.Classes (FunctionField C₀)) ((classMap C₀ hx hy).comp V.subtype)
  change Module.finrank (ZMod 2) (LinearMap.range ((classMap C₀ hx hy).comp V.subtype)) +
    Module.finrank (ZMod 2) (SquareSpace C₀ hx hy V) = Module.finrank (ZMod 2) V at hfirst
  have hsecond := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2)
    (V := SquareSpace C₀ hx hy V) (V₂ := BadData C₀)
    (((badCoordinates C₀).comp V.subtype).comp (SquareSpace C₀ hx hy V).subtype)
  change Module.finrank (ZMod 2) (LinearMap.range (((badCoordinates C₀).comp V.subtype).comp
    (SquareSpace C₀ hx hy V).subtype)) + Module.finrank (ZMod 2) (RegularSpace C₀ hx hy V) =
      Module.finrank (ZMod 2) (SquareSpace C₀ hx hy V) at hsecond
  have hsmall := (LinearMap.range (((badCoordinates C₀).comp V.subtype).comp
    (SquareSpace C₀ hx hy V).subtype)).finrank_le
  rw [badData_finrank] at hsmall
  have hbudget := exceptional_budget C₀ hy
  omega

end PaperP1.CurveCoordinateCut
