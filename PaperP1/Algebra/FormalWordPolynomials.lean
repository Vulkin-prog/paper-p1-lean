module

public import PaperP1.Algebra.BivariateWordSquares
public import Mathlib.Data.Finset.SymmDiff

/-! # The exact overlap and symmetric-difference identities of formal-word polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FormalWordPolynomials

open Finset Polynomial
open scoped symmDiff

def linearOver (R : Type*) [CommRing R] (I : Finset ℤ) : R[X] := ∏ i ∈ I, (X + C (i : R))

def wordOver (R : Type*) [CommRing R] (I J : Finset ℤ) : R[X][X] :=
  C (linearOver R I) * (linearOver R J).map C

theorem product_overlap {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (I J : Finset ι) (f : ι → M) :
    (∏ i ∈ I, f i) * (∏ i ∈ J, f i) =
      (∏ i ∈ I ∆ J, f i) * (∏ i ∈ I ∩ J, f i) ^ 2 := by
  have h := prod_union_inter (s₁ := I) (s₂ := J) (f := f)
  have hu : (I ∆ J) ∪ (I ∩ J) = I ∪ J := symmDiff_sup_inf I J
  have hd : Disjoint (I ∆ J) (I ∩ J) := by
    simpa only [inf_eq_inter] using disjoint_symmDiff_inf I J
  rw [← hu, prod_union hd] at h
  simpa only [pow_two, mul_assoc] using h.symm

theorem linear_overlap (R : Type*) [CommRing R] (I J : Finset ℤ) :
    linearOver R I * linearOver R J = linearOver R (I ∆ J) * linearOver R (I ∩ J) ^ 2 :=
  product_overlap I J _

theorem word_multiply (R : Type*) [CommRing R] (I J K L : Finset ℤ) :
    wordOver R I J * wordOver R K L =
      C (linearOver R I * linearOver R K) * (linearOver R J * linearOver R L).map C := by
  simp only [wordOver, map_mul, Polynomial.map_mul]
  ring

theorem word_overlap (R : Type*) [CommRing R] (I J K L : Finset ℤ) :
    wordOver R I J * wordOver R K L =
      wordOver R (I ∆ K) (J ∆ L) * wordOver R (I ∩ K) (J ∩ L) ^ 2 := by
  rw [word_multiply, linear_overlap, linear_overlap]
  simp only [wordOver, map_mul, map_pow, Polynomial.map_mul, Polynomial.map_pow]
  ring

theorem word_remove_overlap (R : Type*) [CommRing R] (I J K L : Finset ℤ) :
    wordOver R (I ∩ K) (J ∩ L) * wordOver R (K \ I) (L \ J) = wordOver R K L := by
  rw [word_multiply]
  have hx : linearOver R (I ∩ K) * linearOver R (K \ I) = linearOver R K := by
    simpa only [linearOver, inter_comm I K] using prod_inter_mul_prod_sdiff K I
      (fun i : ℤ ↦ (X : R[X]) + C (i : R))
  have hy : linearOver R (J ∩ L) * linearOver R (L \ J) = linearOver R L := by
    simpa only [linearOver, inter_comm J L] using prod_inter_mul_prod_sdiff L J
      (fun i : ℤ ↦ (X : R[X]) + C (i : R))
  rw [hx, hy]
  rfl

theorem rational_word (I J : Finset ℤ) : wordOver ℚ I J = BivariateWordSquares.wordPolynomial I J := rfl

def rationalize : ℤ[X][X] →+* ℚ[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem rationalize_injective : Function.Injective rationalize :=
  Polynomial.map_injective _ (Polynomial.map_injective _ Int.cast_injective)

theorem rationalize_linear (I : Finset ℤ) :
    (linearOver ℤ I).map (Int.castRingHom ℚ) = linearOver ℚ I := by
  simp only [linearOver, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, Int.coe_castRingHom, Int.cast_id]

theorem rationalize_word (I J : Finset ℤ) :
    rationalize (wordOver ℤ I J) = BivariateWordSquares.wordPolynomial I J := by
  change (wordOver ℤ I J).map (Polynomial.mapRingHom (Int.castRingHom ℚ)) = _
  rw [wordOver, Polynomial.map_mul, Polynomial.map_C]
  change C ((linearOver ℤ I).map (Int.castRingHom ℚ)) *
    ((linearOver ℤ J).map C).map (Polynomial.mapRingHom (Int.castRingHom ℚ)) = _
  rw [rationalize_linear, Polynomial.map_map]
  have he : (Polynomial.mapRingHom (Int.castRingHom ℚ)).comp (C (R := ℤ)) =
      (C (R := ℚ)).comp (Int.castRingHom ℚ) := by
    ext n
    simp
  rw [he, ← Polynomial.map_map, rationalize_linear]
  rfl

theorem integer_word_ne_zero (I J : Finset ℤ) : wordOver ℤ I J ≠ 0 := by
  intro h
  apply BivariateWordSquares.wordPolynomial_ne_zero I J
  rw [← rationalize_word, h, map_zero]

end PaperP1.FormalWordPolynomials
