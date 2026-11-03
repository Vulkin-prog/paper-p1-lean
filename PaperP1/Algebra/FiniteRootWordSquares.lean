module

public import PaperP1.Algebra.BivariateWordSquares

/-! # Scaled reduced split words on arbitrary finite field-root sets are nonsquares -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRootWordSquares

open Finset Polynomial

abbrev CoefficientField (F : Type*) [Field F] := FractionRing F[X]
abbrev FunctionField (F : Type*) [Field F] := FractionRing F[X][X]

instance coefficientCharZero (F : Type*) [Field F] [CharZero F] : CharZero (CoefficientField F) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective F[X] (CoefficientField F))

instance functionCharZero (F : Type*) [Field F] [CharZero F] : CharZero (FunctionField F) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective F[X][X] (FunctionField F))

def linear {F : Type*} [Field F] (I : Finset F) : F[X] := ∏ i ∈ I, (X + C i)

def word {F : Type*} [Field F] (I J : Finset F) : F[X][X] := C (linear I) * (linear J).map C

def scaledPolynomial {F : Type*} [Field F] (c : F) (I J : Finset F) : F[X][X] := C (C c) * word I J

def scaledFunction {F : Type*} [Field F] (c : F) (I J : Finset F) : FunctionField F :=
  algebraMap F[X][X] (FunctionField F) (scaledPolynomial c I J)

theorem linear_monic {F : Type*} [Field F] (I : Finset F) : (linear I).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_add_C _)

theorem linear_degree {F : Type*} [Field F] (I : Finset F) : (linear I).natDegree = I.card := by
  unfold linear
  rw [natDegree_prod_of_monic I (fun i : F ↦ (X : F[X]) + C i) (fun _ _ ↦ monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem linear_separable {F : Type*} [Field F] (I : Finset F) : (linear I).Separable := by
  classical
  have hh : (∏ i ∈ I, ((X : F[X]) - C (-i))).Separable :=
    Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ hij ↦ neg_injective hij)
  simpa only [linear, C_neg, sub_neg_eq_add] using hh

theorem polynomial_not_square_right {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (I J : Finset F) (hJ : J.Nonempty) : ¬ IsSquare (scaledPolynomial c I J) := by
  let φ : F[X] →+* CoefficientField F := algebraMap F[X] (CoefficientField F)
  let ψ : F[X][X] →+* (CoefficientField F)[X] := Polynomial.mapRingHom φ
  let a := φ (C c * linear I)
  have ha : a ≠ 0 := by
    intro h
    exact mul_ne_zero (C_ne_zero.mpr hc) (linear_monic I).ne_zero
      (IsFractionRing.injective F[X] (CoefficientField F) (h.trans (map_zero φ).symm))
  have heq : ψ (scaledPolynomial c I J) = C a * (linear J).map (φ.comp C) := by
    change (scaledPolynomial c I J).map φ = _
    simp only [scaledPolynomial, word, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, a, map_mul]
    ring
  have hsep : (ψ (scaledPolynomial c I J)).Separable := by
    rw [heq]
    exact Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)) (linear_separable J).map
  have hn : ¬ IsUnit (ψ (scaledPolynomial c I J)) := by
    intro hunit
    rw [heq] at hunit
    have hdeg := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hunit)
    rw [natDegree_map, linear_degree] at hdeg
    have hcard := hJ.card_pos
    omega
  intro hs
  exact BivariateWordSquares.separable_not_square _ hsep hn (IsSquare.map ψ hs)

theorem polynomial_swap {F : Type*} [Field F] (c : F) (I J : Finset F) :
    Bivariate.swap (scaledPolynomial c I J) = scaledPolynomial c J I := by
  simp only [scaledPolynomial, word, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Polynomial.map_C]
  ring

theorem polynomial_not_square {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (I J : Finset F) (hne : I.Nonempty ∨ J.Nonempty) : ¬ IsSquare (scaledPolynomial c I J) := by
  rcases hne with hI | hJ
  · intro hs
    apply polynomial_not_square_right c hc J I hI
    simpa only [polynomial_swap] using IsSquare.map Bivariate.swap hs
  · exact polynomial_not_square_right c hc I J hJ

theorem function_not_square {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (I J : Finset F) (hne : I.Nonempty ∨ J.Nonempty) : ¬ IsSquare (scaledFunction c I J) := by
  intro hs
  exact polynomial_not_square c hc I J hne
    ((SquareInFractionField.square_reflect (R := F[X][X]) (K := FunctionField F) _).mp hs)

theorem function_ne_zero {F : Type*} [Field F] (c : F) (hc : c ≠ 0) (I J : Finset F) :
    scaledFunction c I J ≠ 0 := by
  have hp : scaledPolynomial c I J ≠ 0 := mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr hc))
    (mul_ne_zero (C_ne_zero.mpr (linear_monic I).ne_zero) (Polynomial.map_ne_zero (linear_monic J).ne_zero))
  intro h
  exact hp (IsFractionRing.injective F[X][X] (FunctionField F) (h.trans (map_zero _).symm))

end PaperP1.FiniteRootWordSquares
