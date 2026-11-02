module

public import PaperP1.Algebra.SquareInFractionField
public import PaperP1.Algebra.RungeSplitProduct
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.Algebra.CharP.Algebra

/-! # Every nonempty reduced formal word gives a nonsquare rational function -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateWordSquares

open Finset Polynomial

def linearProduct (I : Finset ℤ) : ℚ[X] := ∏ i ∈ I, (X + C (i : ℚ))

def wordPolynomial (I J : Finset ℤ) : ℚ[X][X] :=
  C (linearProduct I) * (linearProduct J).map C

abbrev CoefficientField := FractionRing ℚ[X]
abbrev FunctionField := FractionRing ℚ[X][X]

instance : CharZero CoefficientField :=
  charZero_of_injective_algebraMap (IsFractionRing.injective ℚ[X] CoefficientField)

instance : CharZero FunctionField :=
  charZero_of_injective_algebraMap (IsFractionRing.injective ℚ[X][X] FunctionField)

def wordFunction (I J : Finset ℤ) : FunctionField := algebraMap ℚ[X][X] FunctionField (wordPolynomial I J)

theorem linearProduct_monic (I : Finset ℤ) : (linearProduct I).Monic := by
  exact monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_add_C _)

theorem linearProduct_degree (I : Finset ℤ) : (linearProduct I).natDegree = I.card := by
  unfold linearProduct
  rw [natDegree_prod_of_monic I (fun i : ℤ ↦ (X : ℚ[X]) + C (i : ℚ))
    (fun i _ ↦ monic_X_add_C (i : ℚ))]
  simp only [natDegree_X_add_C, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem linearProduct_ne_zero (I : Finset ℤ) : linearProduct I ≠ 0 := (linearProduct_monic I).ne_zero

theorem wordPolynomial_ne_zero (I J : Finset ℤ) : wordPolynomial I J ≠ 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (linearProduct_ne_zero I)
  · exact Polynomial.map_ne_zero (linearProduct_ne_zero J)

theorem wordPolynomial_swap (I J : Finset ℤ) : Bivariate.swap (wordPolynomial I J) = wordPolynomial J I := by
  simp only [wordPolynomial, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, mul_comm]

theorem separable_not_square {F : Type*} [Field F] (p : F[X]) (hp : p.Separable)
    (hn : ¬ IsUnit p) : ¬ IsSquare p := by
  rintro ⟨q, hq⟩
  have hqn : ¬ IsUnit q := by
    intro h
    apply hn
    simpa only [hq] using h.mul h
  have hsep : (q ^ 2).Separable := by simpa only [pow_two, ← hq] using hp
  have htwo := (Polynomial.Separable.of_pow hqn (by decide : 2 ≠ 0) hsep).2
  exact (by decide : (2 : ℕ) ≠ 1) htwo

theorem wordPolynomial_not_square_right (I J : Finset ℤ) (hJ : J.Nonempty) :
    ¬ IsSquare (wordPolynomial I J) := by
  let φ : ℚ[X] →+* CoefficientField := algebraMap ℚ[X] CoefficientField
  let ψ : ℚ[X][X] →+* CoefficientField[X] := Polynomial.mapRingHom φ
  let root : J → CoefficientField := fun j ↦ -((j.val : ℤ) : CoefficientField)
  have hroot : Function.Injective root := by
    intro i j h
    change -((i.val : ℤ) : CoefficientField) = -((j.val : ℤ) : CoefficientField) at h
    have hc := neg_injective h
    have hv : i.val = j.val := Int.cast_injective hc
    exact Subtype.ext hv
  have hprod : (linearProduct J).map (φ.comp C) = RungeSplitProduct.splitProduct root := by
    simp only [linearProduct, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_intCast, map_intCast, RungeSplitProduct.splitProduct, root, map_neg,
      sub_neg_eq_add]
    exact (Finset.prod_coe_sort J (fun z : ℤ ↦ (X : CoefficientField[X]) + (z : CoefficientField[X]))).symm
  have hφI : φ (linearProduct I) ≠ 0 := by
    intro h
    apply linearProduct_ne_zero I
    exact IsFractionRing.injective ℚ[X] CoefficientField (h.trans (map_zero φ).symm)
  have hψ : ψ (wordPolynomial I J) = C (φ (linearProduct I)) * RungeSplitProduct.splitProduct root := by
    change (wordPolynomial I J).map φ = _
    rw [wordPolynomial, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hprod]
  have hsep : (ψ (wordPolynomial I J)).Separable := by
    rw [hψ]
    exact Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hφI))
      ((RungeSplitProduct.splitProduct_separable_iff root).mpr hroot)
  have hn : ¬ IsUnit (ψ (wordPolynomial I J)) := by
    intro h
    rw [hψ] at h
    have hu := isUnit_of_mul_isUnit_right h
    have hd := natDegree_eq_zero_of_isUnit hu
    rw [RungeSplitProduct.natDegree_splitProduct] at hd
    have hc : 0 < Fintype.card J := by simpa only [Fintype.card_coe] using hJ.card_pos
    omega
  intro hs
  exact separable_not_square _ hsep hn (IsSquare.map ψ hs)

theorem wordPolynomial_not_square (I J : Finset ℤ) (hne : I.Nonempty ∨ J.Nonempty) :
    ¬ IsSquare (wordPolynomial I J) := by
  rcases hne with hI | hJ
  · intro hs
    apply wordPolynomial_not_square_right J I hI
    simpa only [wordPolynomial_swap] using IsSquare.map Bivariate.swap hs
  · exact wordPolynomial_not_square_right I J hJ

theorem wordFunction_not_square (I J : Finset ℤ) (hne : I.Nonempty ∨ J.Nonempty) :
    ¬ IsSquare (wordFunction I J) := by
  intro hs
  apply wordPolynomial_not_square I J hne
  exact (SquareInFractionField.square_reflect (R := ℚ[X][X]) (K := FunctionField) _).mp hs

end PaperP1.BivariateWordSquares
