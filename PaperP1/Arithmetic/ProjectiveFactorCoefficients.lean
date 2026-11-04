module

public import PaperP1.Arithmetic.BivariateProjectiveSwap

/-! # Every literal projective coefficient and its exact height are recovered -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveFactorCoefficients

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.IntegerFactorProjectiveCurve
open PaperP1.DeterminantAuxiliaryBiform PaperP1.BiquadraticCoefficientPolynomials
open PaperP1.BivariateProjectiveSwap

theorem projective_coefficient (G : ℤ[X][X]) (m n : Fin 2 →₀ ℕ) :
    ((projective G).coeff m).coeff n =
      if m 0 + m 1 = degreeX G ∧ n 0 + n 1 = degreeY G then (G.coeff (n 0)).coeff (m 0) else 0 := by
  unfold projective biform
  rw [Polynomial.coeff_homogenize]
  by_cases hm : m 0 + m 1 = degreeX G
  · rw [ite_eq_left hm]
    let a : Fin (degreeX G + 1) := ⟨m 0, by omega⟩
    change ((outerPolynomial (degreeX G) (degreeY G) (coefficients G)).coeff a.val).coeff n = _
    rw [outer_coefficient]
    unfold forms
    rw [Polynomial.coeff_homogenize]
    by_cases hn : n 0 + n 1 = degreeY G
    · rw [ite_eq_left hn]
      let b : Fin (degreeY G + 1) := ⟨n 0, by omega⟩
      change (row (degreeY G) (fun b ↦ coefficients G (a, b))).coeff b.val = _
      rw [row_coefficient]
      simp [coefficients, a, b, hm, hn]
    · simp [hm, hn]
  · simp [hm]

theorem projective_coefficient_swap (G : ℤ[X][X]) (m n : Fin 2 →₀ ℕ) :
    ((projective (Bivariate.swap G)).coeff m).coeff n = ((projective G).coeff n).coeff m := by
  rw [projective_coefficient, projective_coefficient]
  simp only [degreeX_swap, degreeY_swap, coeff_swap, and_comm]

theorem coefficient_homogeneous (G : ℤ[X][X]) (m : Fin 2 →₀ ℕ) :
    ((projective G).coeff m).IsHomogeneous (degreeY G) := by
  intro n hn
  have hdeg : n 0 + n 1 = degreeY G := by
    by_contra hh
    rw [projective_coefficient] at hn
    simp only [hh, and_false, ite_false, ne_eq, not_true_eq_false] at hn
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hdeg

theorem height_iff (G : ℤ[X][X]) (H : ℕ) :
    (∀ m n, |((projective G).coeff m).coeff n| ≤ (H : ℤ)) ↔ height G ≤ H := by
  constructor
  · intro hh
    have hc := BiformCoefficientRecovery.coefficient_bound_from_biform (degreeX G) (degreeY G) H (coefficients G) hh
    have ht := DeterminantAuxiliaryPolynomial.rectangle_height_le (degreeX G) (degreeY G) H (coefficients G) hc
    simpa only [reconstruction] using ht
  · intro hH m n
    exact (projective_height G m n).trans (by exact_mod_cast hH)

end PaperP1.ProjectiveFactorCoefficients
