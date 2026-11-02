module

public import PaperP1.Algebra.FormalWordPolynomials

/-! # Scalar multiples of nonempty reduced split words remain nonsquares over every characteristic-zero base field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledSplitWordSquares

open Finset Polynomial PaperP1.FormalWordPolynomials

abbrev CoefficientField (F : Type*) [Field F] := FractionRing F[X]
abbrev FunctionField (F : Type*) [Field F] := FractionRing F[X][X]

instance coefficientCharZero (F : Type*) [Field F] [CharZero F] : CharZero (CoefficientField F) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective F[X] (CoefficientField F))

instance functionCharZero (F : Type*) [Field F] [CharZero F] : CharZero (FunctionField F) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective F[X][X] (FunctionField F))

def scaledPolynomial {F : Type*} [Field F] (c : F) (I J : Finset ℤ) : F[X][X] :=
  C (C c) * wordOver F I J

def scaledFunction {F : Type*} [Field F] (c : F) (I J : Finset ℤ) : FunctionField F :=
  algebraMap F[X][X] (FunctionField F) (scaledPolynomial c I J)

theorem linear_monic {F : Type*} [Field F] (I : Finset ℤ) : (linearOver F I).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_add_C _)

theorem linear_degree {F : Type*} [Field F] (I : Finset ℤ) : (linearOver F I).natDegree = I.card := by
  unfold linearOver
  rw [natDegree_prod_of_monic I (fun i : ℤ ↦ (X : F[X]) + C (i : F)) (fun _ _ ↦ monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem linear_separable {F : Type*} [Field F] [CharZero F] (I : Finset ℤ) : (linearOver F I).Separable := by
  let roots : I → F := fun i ↦ -((i.val : ℤ) : F)
  have hinj : Function.Injective roots := by
    intro i j hij
    apply Subtype.ext
    exact Int.cast_injective (neg_injective hij)
  have heq : linearOver F I = RungeSplitProduct.splitProduct roots := by
    simp only [linearOver, RungeSplitProduct.splitProduct, roots, map_neg, sub_neg_eq_add]
    exact (prod_coe_sort I (fun i : ℤ ↦ (X : F[X]) + C (i : F))).symm
  rw [heq]
  exact (RungeSplitProduct.splitProduct_separable_iff roots).mpr hinj

theorem polynomial_not_square_right {F : Type*} [Field F] [CharZero F]
    (c : F) (hc : c ≠ 0) (I J : Finset ℤ) (hJ : J.Nonempty) :
    ¬ IsSquare (scaledPolynomial c I J) := by
  let φ : F[X] →+* CoefficientField F := algebraMap F[X] (CoefficientField F)
  let ψ : F[X][X] →+* (CoefficientField F)[X] := Polynomial.mapRingHom φ
  let a := φ (C c * linearOver F I)
  have ha : a ≠ 0 := by
    intro h
    apply mul_ne_zero (C_ne_zero.mpr hc) (linear_monic I).ne_zero
    exact IsFractionRing.injective F[X] (CoefficientField F) (h.trans (map_zero φ).symm)
  have heq : ψ (scaledPolynomial c I J) = C a * (linearOver F J).map (φ.comp C) := by
    change (scaledPolynomial c I J).map φ = _
    simp only [scaledPolynomial, wordOver, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, a, map_mul]
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

theorem polynomial_swap {F : Type*} [Field F] (c : F) (I J : Finset ℤ) :
    Bivariate.swap (scaledPolynomial c I J) = scaledPolynomial c J I := by
  simp only [scaledPolynomial, wordOver, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Polynomial.map_C]
  ring

theorem polynomial_not_square {F : Type*} [Field F] [CharZero F]
    (c : F) (hc : c ≠ 0) (I J : Finset ℤ) (hne : I.Nonempty ∨ J.Nonempty) :
    ¬ IsSquare (scaledPolynomial c I J) := by
  rcases hne with hI | hJ
  · intro hs
    apply polynomial_not_square_right c hc J I hI
    simpa only [polynomial_swap] using IsSquare.map Bivariate.swap hs
  · exact polynomial_not_square_right c hc I J hJ

theorem function_not_square {F : Type*} [Field F] [CharZero F]
    (c : F) (hc : c ≠ 0) (I J : Finset ℤ) (hne : I.Nonempty ∨ J.Nonempty) :
    ¬ IsSquare (scaledFunction c I J) := by
  intro hs
  exact polynomial_not_square c hc I J hne
    ((SquareInFractionField.square_reflect (R := F[X][X]) (K := FunctionField F) _).mp hs)

theorem function_ne_zero {F : Type*} [Field F] [CharZero F]
    (c : F) (hc : c ≠ 0) (I J : Finset ℤ) : scaledFunction c I J ≠ 0 := by
  have hp : scaledPolynomial c I J ≠ 0 := mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr hc))
    (mul_ne_zero (C_ne_zero.mpr (linear_monic I).ne_zero) (Polynomial.map_ne_zero (linear_monic J).ne_zero))
  intro h
  apply hp
  exact IsFractionRing.injective F[X][X] (FunctionField F) (h.trans (map_zero _).symm)

end PaperP1.ScaledSplitWordSquares
