module

public import PaperP1.Algebra.CurveFunctionField
public import PaperP1.Algebra.FieldSquareClasses
public import PaperP1.Algebra.PairwiseEqualSpan
public import PaperP1.Arithmetic.CurveNormCollapse

/-! # Pair norms on an actual irreducible curve force a one-dimensional image -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveWordSquareClasses

open Polynomial PaperP1.BivariateDegrees PaperP1.FormalWordPolynomials
  PaperP1.BiquadraticWordNorm PaperP1.CurveFunctionField PaperP1.FieldSquareClasses

local instance : CommRing ℤ[X][X] := inferInstance
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def wordClass (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) (I J : Finset ℤ) : Classes (FunctionField C₀) :=
  ofNonzero (specialize C₀ (wordOver ℤ I J)) (word_ne_zero C₀ hdx hdy I J)

theorem pair_dependence (C₀ : ℤ[X][X]) [hC : Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀)
    (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X])
    (hprimitive : ∀ E : ℤ[X][X], (∀ χ, E ∣ A χ) → IsUnit E)
    (hdiv : C₀ ∣ normPolynomial I J K L A) :
    IsSquare (specialize C₀ (wordOver ℤ I J)) ∨ IsSquare (specialize C₀ (wordOver ℤ K L)) ∨
      IsSquare (specialize C₀ (wordOver ℤ I J) * specialize C₀ (wordOver ℤ K L)) := by
  let : CharZero (FunctionField C₀) := functionField_charZero C₀ hdy
  exact CurveNormCollapse.dependent_on_curve (specialize C₀) C₀ hC.out.not_isUnit
    (specialize_zero_iff C₀) I J K L A hprimitive
    (word_ne_zero C₀ hdx hdy I J) (word_ne_zero C₀ hdx hdy K L) hdiv

theorem pair_classes (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀)
    (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X])
    (hprimitive : ∀ E : ℤ[X][X], (∀ χ, E ∣ A χ) → IsUnit E)
    (hdiv : C₀ ∣ normPolynomial I J K L A) :
    wordClass C₀ hdx hdy I J = 0 ∨ wordClass C₀ hdx hdy K L = 0 ∨
      wordClass C₀ hdx hdy I J = wordClass C₀ hdx hdy K L :=
  (pair_dependence_iff _ _ (word_ne_zero C₀ hdx hdy I J) (word_ne_zero C₀ hdx hdy K L)).mp
    (pair_dependence C₀ hdx hdy I J K L A hprimitive hdiv)

theorem pairwise_image_rank {ι : Type*} (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀)
    (I J : ι → Finset ℤ) (A : ι → ι → Fin 4 → ℤ[X][X])
    (hprimitive : ∀ i j, i ≠ j → ∀ E : ℤ[X][X], (∀ χ, E ∣ A i j χ) → IsUnit E)
    (hdiv : ∀ i j, i ≠ j → C₀ ∣ normPolynomial (I i) (J i) (I j) (J j) (A i j)) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun i ↦ wordClass C₀ hdx hdy (I i) (J i)))) ≤ 1 := by
  apply PairwiseEqualSpan.finrank_le_one (K := ZMod 2) (M := Classes (FunctionField C₀))
    (fun i : ι ↦ wordClass C₀ hdx hdy (I i) (J i))
  intro i j
  by_cases hij : i = j
  · exact Or.inr (Or.inr (by rw [hij]))
  · exact pair_classes C₀ hdx hdy (I i) (J i) (I j) (J j) (A i j)
      (hprimitive i j hij) (hdiv i j hij)

end PaperP1.CurveWordSquareClasses
