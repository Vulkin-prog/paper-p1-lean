module

public import PaperP1.Algebra.RationalBivariateIrreducibility
public import PaperP1.Algebra.BivariateHeight
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Exact coprime coefficient polynomials of the actual first-degree-one factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearBivariateCoefficients

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.RationalBivariateIrreducibility

def firstCoefficient (G : ℤ[X][X]) : ℤ[X] := (Bivariate.swap G).coeff 1
def secondCoefficient (G : ℤ[X][X]) : ℤ[X] := (Bivariate.swap G).coeff 0

theorem degreeX_le_of_coeff_bound (P : ℤ[X][X]) (H : ℕ)
    (h : ∀ i, (P.coeff i).natDegree ≤ H) : degreeX P ≤ H := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  apply Polynomial.ext
  intro i
  rw [coeff_swap]
  exact coeff_eq_zero_of_natDegree_lt ((h i).trans_lt hj)

theorem degreeX_eq_max_coefficients (P : ℤ[X][X]) (hP : P.natDegree ≤ 1) :
    degreeX P = max (P.coeff 0).natDegree (P.coeff 1).natDegree := by
  apply Nat.le_antisymm
  · apply degreeX_le_of_coeff_bound
    intro i
    by_cases h0 : i = 0
    · subst i
      exact Nat.le_max_left _ _
    · by_cases h1 : i = 1
      · subst i
        exact Nat.le_max_right _ _
      · have hi : P.natDegree < i := by omega
        rw [coeff_eq_zero_of_natDegree_lt hi, natDegree_zero]
        exact Nat.zero_le _
  · exact max_le (natDegree_coeff_le_degreeX P 0) (natDegree_coeff_le_degreeX P 1)

theorem linear_coefficients_relprime {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : Irreducible p) (hdegree : p.natDegree = 1) : IsRelPrime (p.coeff 1) (p.coeff 0) := by
  intro r hr1 hr0
  apply (hp.isPrimitive (by omega)) r
  rw [eq_X_add_C_of_natDegree_le_one (by omega : p.natDegree ≤ 1)]
  exact dvd_add (dvd_mul_of_dvd_left (map_dvd Polynomial.C hr1) X) (map_dvd Polynomial.C hr0)

theorem coefficient_degree_bounds (G : ℤ[X][X]) :
    (firstCoefficient G).natDegree ≤ degreeY G ∧ (secondCoefficient G).natDegree ≤ degreeY G := by
  constructor
  · simpa only [firstCoefficient, degreeX, degreeY, Bivariate.swap_swap_apply] using natDegree_coeff_le_degreeX (Bivariate.swap G) 1
  · simpa only [secondCoefficient, degreeX, degreeY, Bivariate.swap_swap_apply] using natDegree_coeff_le_degreeX (Bivariate.swap G) 0

theorem coefficient_full_degree (G : ℤ[X][X]) (hG : degreeX G = 1) :
    (firstCoefficient G).natDegree = degreeY G ∨ (secondCoefficient G).natDegree = degreeY G := by
  have hP : (Bivariate.swap G).natDegree ≤ 1 := hG.le
  have hm : max (secondCoefficient G).natDegree (firstCoefficient G).natDegree = degreeY G := by
    simpa only [firstCoefficient, secondCoefficient, degreeX, degreeY, Bivariate.swap_swap_apply] using
      (degreeX_eq_max_coefficients (Bivariate.swap G) hP).symm
  by_cases h : (secondCoefficient G).natDegree ≤ (firstCoefficient G).natDegree
  · exact Or.inl (by simpa only [max_eq_right h] using hm)
  · have h' : (firstCoefficient G).natDegree ≤ (secondCoefficient G).natDegree := by omega
    exact Or.inr (by simpa only [max_eq_left h'] using hm)

theorem coefficients_coprime (G : ℤ[X][X]) (hG : Irreducible G) (hdegree : degreeX G = 1) :
    IsCoprime ((firstCoefficient G).map (Int.castRingHom ℚ)) ((secondCoefficient G).map (Int.castRingHom ℚ)) := by
  let P := Bivariate.swap G
  have hP : Irreducible P := (MulEquiv.irreducible_iff (Bivariate.swap (R := ℤ))).mpr hG
  have hPdegree : P.natDegree = 1 := hdegree
  have hpositive : 0 < IntegerBivariateFactorCover.degreeSum P := by
    unfold IntegerBivariateFactorCover.degreeSum degreeY
    omega
  have hQ := rational_irreducible P hP hpositive
  have hmap : Function.Injective (Polynomial.mapRingHom (Int.castRingHom ℚ)) :=
    Polynomial.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  have hQdegree : (rationalize P).natDegree = 1 := by
    rw [rationalize, natDegree_map_eq_of_injective hmap]
    exact hPdegree
  have hcoeff : IsCoprime ((rationalize P).coeff 1) ((rationalize P).coeff 0) :=
    (linear_coefficients_relprime (rationalize P) hQ hQdegree).isCoprime
  simpa [rationalize, firstCoefficient, secondCoefficient, P] using hcoeff

theorem coefficient_height (G : ℤ[X][X]) :
    (∀ j, ((firstCoefficient G).coeff j).natAbs ≤ height G) ∧
      ∀ j, ((secondCoefficient G).coeff j).natAbs ≤ height G := by
  constructor
  · intro j
    unfold firstCoefficient
    rw [coeff_swap]
    exact coefficient_natAbs_le_height G j 1
  · intro j
    unfold secondCoefficient
    rw [coeff_swap]
    exact coefficient_natAbs_le_height G j 0

end PaperP1.LinearBivariateCoefficients
