module

public import PaperP1.Algebra.BivariateDegrees
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # A nonconstant irreducible bivariate factor has a nonzero resultant unless it divides -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateResultantNonzero

open Polynomial PaperP1.BivariateDegrees

theorem nonzero_of_not_dvd (C₀ P : ℤ[X][X]) (hC : Irreducible C₀)
    (hdegree : 0 < degreeY C₀) (hnot : ¬ C₀ ∣ P) : C₀.resultant P ≠ 0 := by
  let K := FractionRing ℤ[X]
  let φ : ℤ[X] →+* K := algebraMap ℤ[X] K
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ[X] K
  have hprimitive : C₀.IsPrimitive := hC.isPrimitive (by change C₀.natDegree ≠ 0; exact ne_of_gt hdegree)
  have hirr : Irreducible (C₀.map φ) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hC
  have hnd : ¬ C₀.map φ ∣ P.map φ := by
    intro h
    exact hnot ((hprimitive.dvd_iff_fraction_map_dvd_fraction_map K).mpr h)
  have hcop : IsCoprime (C₀.map φ) (P.map φ) := hirr.coprime_iff_not_dvd.mpr hnd
  have hn := Polynomial.resultant_ne_zero (C₀.map φ) (P.map φ) hcop
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ] at hn
  intro hz
  apply hn
  rw [Polynomial.resultant_map_map, hz, map_zero]

end PaperP1.BivariateResultantNonzero
