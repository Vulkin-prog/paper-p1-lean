module

public import PaperP1.Algebra.HomogeneousSplitRadicalData
public import PaperP1.Algebra.TrivariatePolynomialEquiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Exact ordinary homogeneity of the literal homogenized radicands

The native variables, in the order of `threeEquiv`, are `(Y,X,Z)`.
This concerns the base polynomials; no projective degree formula is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalPolynomials

open Finset Polynomial PaperP1.HomogeneousSplitRadicalData
  PaperP1.TrivariatePolynomialEquiv

def nativeLinear (F : Type*) [Field F] (j : Fin 3) (I : Finset ℤ) : MvPolynomial (Fin 3) F :=
  ∏ i ∈ I, (MvPolynomial.X j + MvPolynomial.C (i : F) * MvPolynomial.X 2)

def nativeRadicand {F : Type*} [Field F] (c : F) (e : ℕ) (I J : Finset ℤ) : MvPolynomial (Fin 3) F :=
  (MvPolynomial.C c * MvPolynomial.X 2 ^ e) * nativeLinear F 1 I * nativeLinear F 0 J

theorem threeEquiv_C (F : Type*) [Field F] (c : F) :
    threeEquiv F (MvPolynomial.C c) = C (C (C c)) := by
  exact (threeEquiv F).commutes c

theorem nativeLinear_left_map (F : Type*) [Field F] (I : Finset ℤ) :
    threeEquiv F (nativeLinear F 1 I) = C (linear F I) := by
  have hc : ∀ i : ℤ, C (i : F) = (i : F[X]) := by intro i; simp
  simp only [nativeLinear, linear, map_prod, map_add, map_mul, threeEquiv_C,
    threeEquiv_X_one, threeEquiv_X_two, hc]

theorem nativeLinear_right_map (F : Type*) [Field F] (J : Finset ℤ) :
    threeEquiv F (nativeLinear F 0 J) = (linear F J).map C := by
  have hc : ∀ i : ℤ, C (i : F) = (i : F[X]) := by intro i; simp
  simp only [nativeLinear, linear, map_prod, map_add, map_mul, threeEquiv_C,
    threeEquiv_X_zero, threeEquiv_X_two, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, hc]

theorem nativeRadicand_map {F : Type*} [Field F] (c : F) (e : ℕ) (I J : Finset ℤ) :
    threeEquiv F (nativeRadicand c e I J) = radicand c e I J := by
  simp only [nativeRadicand, radicand, word, map_mul, map_pow, threeEquiv_C,
    threeEquiv_X_two, nativeLinear_left_map, nativeLinear_right_map, mul_assoc]

theorem asMvPolynomial_radicand {F : Type*} [Field F] (c : F) (e : ℕ) (I J : Finset ℤ) :
    asMvPolynomial F (radicand c e I J) = nativeRadicand c e I J := by
  apply (threeEquiv F).injective
  rw [asMvPolynomial, AlgEquiv.apply_symm_apply, nativeRadicand_map]

theorem nativeLinear_homogeneous (F : Type*) [Field F] (j : Fin 3) (I : Finset ℤ) :
    (nativeLinear F j I).IsHomogeneous I.card := by
  simpa only [nativeLinear, sum_const, smul_eq_mul, mul_one] using
    MvPolynomial.IsHomogeneous.prod I
      (fun i : ℤ ↦ MvPolynomial.X j + MvPolynomial.C (i : F) * MvPolynomial.X (2 : Fin 3))
      (fun _ ↦ 1) (fun i _ ↦ (MvPolynomial.isHomogeneous_X F j).add
        (MvPolynomial.isHomogeneous_C_mul_X (i : F) (2 : Fin 3)))

theorem nativeRadicand_homogeneous {F : Type*} [Field F]
    (c : F) (e : ℕ) (I J : Finset ℤ) :
    (nativeRadicand c e I J).IsHomogeneous (e + I.card + J.card) := by
  exact ((MvPolynomial.isHomogeneous_C_mul_X_pow c (2 : Fin 3) e).mul
    (nativeLinear_homogeneous F 1 I)).mul (nativeLinear_homogeneous F 0 J)

theorem homogenized_homogeneous {F : Type*} [Field F]
    (c : F) (D : ℕ) (I J : Finset ℤ) (hD : I.card + J.card ≤ 2 * D) :
    (asMvPolynomial F (radicand c (2 * D - (I.card + J.card)) I J)).IsHomogeneous (2 * D) := by
  rw [asMvPolynomial_radicand]
  convert nativeRadicand_homogeneous c (2 * D - (I.card + J.card)) I J using 1; omega

theorem linear_monic (F : Type*) [Field F] (I : Finset ℤ) : (linear F I).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_add_C _)

theorem radicand_ne_zero {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (e : ℕ) (I J : Finset ℤ) : radicand c e I J ≠ 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (C_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ X_ne_zero)))
  · exact mul_ne_zero (C_ne_zero.mpr (linear_monic F I).ne_zero)
      ((Polynomial.map_ne_zero_iff C_injective).mpr (linear_monic F J).ne_zero)

theorem nativeRadicand_ne_zero {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (e : ℕ) (I J : Finset ℤ) : nativeRadicand c e I J ≠ 0 := by
  intro hh
  apply radicand_ne_zero c hc e I J
  rw [← nativeRadicand_map, hh, map_zero]

theorem nativeRadicand_totalDegree {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (e : ℕ) (I J : Finset ℤ) :
    (nativeRadicand c e I J).totalDegree = e + I.card + J.card :=
  (nativeRadicand_homogeneous c e I J).totalDegree (nativeRadicand_ne_zero c hc e I J)

theorem homogenized_totalDegree {F : Type*} [Field F]
    (c : F) (hc : c ≠ 0) (D : ℕ) (I J : Finset ℤ) (hD : I.card + J.card ≤ 2 * D) :
    (asMvPolynomial F (radicand c (2 * D - (I.card + J.card)) I J)).totalDegree = 2 * D := by
  rw [asMvPolynomial_radicand, nativeRadicand_totalDegree c hc]
  omega

end PaperP1.HomogeneousSplitRadicalPolynomials
