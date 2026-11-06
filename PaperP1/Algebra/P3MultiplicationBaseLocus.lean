module

public import PaperP1.Algebra.P3CoefficientMultiplication
public import PaperP1.Algebra.RankOneTensorFactorization

/-! # The actual universal multiplication coefficients have no nonzero rank-one base point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3MultiplicationBaseLocus

open MvPolynomial P3HomogeneousCoefficientFamily P3CoefficientMultiplication
open scoped Classical

theorem exists_nonzero_coefficient {F : Type*} [Field F] (e f : ℕ)
    (z : Index e × Index f → F) (hz : z ≠ 0)
    (hminor : ∀ (i k : Index e) (j l : Index f), z (i, j) * z (k, l) = z (i, l) * z (k, j)) :
    ∃ m : Index (e + f), eval z (map (Int.castRingHom F) (coefficientForm e f m)) ≠ 0 := by
  obtain ⟨a, b, ha, hb, he⟩ := RankOneTensorFactorization.exists_factors z hz hminor
  have hzeq : z = fun ij ↦ a ij.1 * b ij.2 := funext he
  have hpoly : tensorPolynomial e f z ≠ 0 := by
    rw [hzeq]
    exact pure_tensor_nonzero e f a b ha hb
  by_contra hn
  have hzcoef : ∀ m : Index (e + f),
      eval z (map (Int.castRingHom F) (coefficientForm e f m)) = 0 := by
    intro m
    exact Classical.not_not.mp (fun h ↦ hn ⟨m, h⟩)
  apply hpoly
  rw [← reconstruct_tensor]
  simp only [polynomial, hzcoef, monomial_zero, Finset.sum_const_zero]

theorem all_coefficients_zero_iff {F : Type*} [Field F] (e f : ℕ)
    (z : Index e × Index f → F)
    (hminor : ∀ (i k : Index e) (j l : Index f), z (i, j) * z (k, l) = z (i, l) * z (k, j)) :
    (∀ m : Index (e + f), eval z (map (Int.castRingHom F) (coefficientForm e f m)) = 0) ↔ z = 0 := by
  constructor
  · intro hzero
    by_contra hz
    obtain ⟨m, hm⟩ := exists_nonzero_coefficient e f z hz hminor
    exact hm (hzero m)
  · rintro rfl m
    rw [evaluate_form]
    simp

end PaperP1.P3MultiplicationBaseLocus
