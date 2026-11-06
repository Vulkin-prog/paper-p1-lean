module

public import PaperP1.Algebra.P3HomogeneousCoefficientFamily
public import PaperP1.Algebra.P3CoefficientFieldTransport

/-! # Actual universal integer linear forms for multiplication of homogeneous coefficient families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CoefficientMultiplication

open MvPolynomial Finset P3HomogeneousCoefficientFamily
open scoped Classical

def coefficientForm (e f : ℕ) (m : Index (e + f)) : MvPolynomial (Index e × Index f) ℤ :=
  ∑ i, ∑ j, if i.val + j.val = m.val then X (i, j) else 0

def tensorPolynomial {R : Type*} [CommRing R] (e f : ℕ) (z : Index e × Index f → R) :
    MvPolynomial (Fin 4) R := ∑ i, ∑ j, monomial (i.val + j.val) (z (i, j))

theorem form_homogeneous (e f : ℕ) (m : Index (e + f)) :
    (coefficientForm e f m).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  split_ifs
  · exact isHomogeneous_X ℤ (i, j)
  · exact isHomogeneous_zero _ _ _

theorem evaluate_form {R : Type*} [CommRing R] (e f : ℕ) (m : Index (e + f))
    (z : Index e × Index f → R) :
    eval z (map (Int.castRingHom R) (coefficientForm e f m)) =
      ∑ i, ∑ j, if i.val + j.val = m.val then z (i, j) else 0 := by
  simp only [coefficientForm, map_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem tensor_coefficient {R : Type*} [CommRing R] (e f : ℕ)
    (z : Index e × Index f → R) (m : Fin 4 →₀ ℕ) :
    (tensorPolynomial e f z).coeff m = ∑ i, ∑ j, if i.val + j.val = m then z (i, j) else 0 := by
  simp only [tensorPolynomial, coeff_sum, coeff_monomial]

theorem tensor_homogeneous {R : Type*} [CommRing R] (e f : ℕ) (z : Index e × Index f → R) :
    (tensorPolynomial e f z).IsHomogeneous (e + f) := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  apply isHomogeneous_monomial
  simp only [map_add, i.property, j.property]

theorem reconstruct_tensor {R : Type*} [CommRing R] (e f : ℕ) (z : Index e × Index f → R) :
    polynomial (e + f) (fun m ↦ eval z (map (Int.castRingHom R) (coefficientForm e f m))) =
      tensorPolynomial e f z := by
  have he : (fun m : Index (e + f) ↦ eval z (map (Int.castRingHom R) (coefficientForm e f m))) =
      (fun m : Index (e + f) ↦ (tensorPolynomial e f z).coeff m.val) := by
    funext m
    rw [evaluate_form, tensor_coefficient]
  rw [he]
  exact reconstruct (e + f) _ (tensor_homogeneous e f z)

theorem pure_tensor_product {R : Type*} [CommRing R] (e f : ℕ) (a : Index e → R) (b : Index f → R) :
    tensorPolynomial e f (fun ij ↦ a ij.1 * b ij.2) = polynomial e a * polynomial f b := by
  simp only [tensorPolynomial, polynomial, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
  rw [sum_comm]

theorem pure_tensor_nonzero {F : Type*} [Field F] (e f : ℕ) (a : Index e → F) (b : Index f → F)
    (ha : a ≠ 0) (hb : b ≠ 0) : tensorPolynomial e f (fun ij ↦ a ij.1 * b ij.2) ≠ 0 := by
  rw [pure_tensor_product]
  exact mul_ne_zero (nonzero e a ha) (nonzero f b hb)

end PaperP1.P3CoefficientMultiplication
