module

public import PaperP1.Arithmetic.CurveWordSquareClasses
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The actual linear square-class map on formal words along a curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveWordMap

open Polynomial PaperP1.BivariateDegrees PaperP1.FormalWordPolynomials
  PaperP1.CurveFunctionField PaperP1.FieldSquareClasses PaperP1.CurveWordSquareClasses

local instance : CommRing ℤ[X][X] := inferInstance
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Words := (ℤ →₀ ZMod 2) × (ℤ →₀ ZMod 2)

def encode (I : Finset ℤ) : ℤ →₀ ZMod 2 := ∑ i ∈ I, Finsupp.single i 1

def firstClass (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hdy : 0 < degreeY C₀) (i : ℤ) :
    Classes (FunctionField C₀) :=
  ofNonzero (specialize C₀ (C (X + C i))) (first_linear_ne_zero C₀ hdy i)

def secondClass (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hdx : 0 < degreeX C₀) (i : ℤ) :
    Classes (FunctionField C₀) :=
  ofNonzero (specialize C₀ (X + C (C i))) (second_linear_ne_zero C₀ hdx i)

def classMap (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) : Words →ₗ[ZMod 2] Classes (FunctionField C₀) :=
  (Finsupp.linearCombination (ZMod 2) (firstClass C₀ hdy)).coprod
    (Finsupp.linearCombination (ZMod 2) (secondClass C₀ hdx))

theorem wordClass_sum (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) (I J : Finset ℤ) :
    wordClass C₀ hdx hdy I J = (∑ i ∈ I, firstClass C₀ hdy i) + ∑ j ∈ J, secondClass C₀ hdx j := by
  have hx : specialize C₀ (C (linearOver ℤ I)) = ∏ i ∈ I, specialize C₀ (C (X + C i)) := by
    simp only [linearOver, map_prod, Int.cast_id]
  have hy : specialize C₀ ((linearOver ℤ J).map C) = ∏ j ∈ J, specialize C₀ (X + C (C j)) := by
    simp only [linearOver, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, map_C, map_prod, Int.cast_id]
  simp only [wordClass, wordOver, map_mul, hx, hy, ofNonzero_mul]
  rw [ofNonzero_prod I _ (first_linear_ne_zero C₀ hdy), ofNonzero_prod J _ (second_linear_ne_zero C₀ hdx)]
  rfl

theorem classMap_encode (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) (I J : Finset ℤ) :
    classMap C₀ hdx hdy (encode I, encode J) = wordClass C₀ hdx hdy I J := by
  rw [wordClass_sum]
  simp [classMap, encode]

theorem image_eq_basis_span {ι : Type*} (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words)
    (b : Module.Basis ι (ZMod 2) V) (I J : ι → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i))) :
    V.map (classMap C₀ hdx hdy) = Submodule.span (ZMod 2)
      (Set.range (fun i ↦ wordClass C₀ hdx hdy (I i) (J i))) := by
  calc
    V.map (classMap C₀ hdx hdy) =
        (Submodule.map V.subtype ⊤).map (classMap C₀ hdx hdy) := by rw [V.map_subtype_top]
    _ = ((Submodule.span (ZMod 2) (Set.range b)).map V.subtype).map (classMap C₀ hdx hdy) := by rw [b.span_eq]
    _ = Submodule.span (ZMod 2) (Set.range (fun i ↦ wordClass C₀ hdx hdy (I i) (J i))) := by
      rw [Submodule.map_span, Submodule.map_span]
      simp only [← Set.range_comp]
      congr 2
      funext i
      change classMap C₀ hdx hdy (b i : Words) = wordClass C₀ hdx hdy (I i) (J i)
      rw [hwords, classMap_encode]

theorem image_rank_le_one {ι : Type*} (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) (V : Submodule (ZMod 2) Words)
    (b : Module.Basis ι (ZMod 2) V) (I J : ι → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i)))
    (A : ι → ι → Fin 4 → ℤ[X][X])
    (hprimitive : ∀ i j, i ≠ j → ∀ E : ℤ[X][X], (∀ χ, E ∣ A i j χ) → IsUnit E)
    (hdiv : ∀ i j, i ≠ j → C₀ ∣ PaperP1.BiquadraticWordNorm.normPolynomial (I i) (J i) (I j) (J j) (A i j)) :
    Module.finrank (ZMod 2) (V.map (classMap C₀ hdx hdy)) ≤ 1 := by
  rw [image_eq_basis_span C₀ hdx hdy V b I J hwords]
  exact pairwise_image_rank C₀ hdx hdy I J A hprimitive hdiv

end PaperP1.CurveWordMap
