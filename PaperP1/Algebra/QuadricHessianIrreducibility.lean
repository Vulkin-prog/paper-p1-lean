module

public import PaperP1.Algebra.HomogeneousQuadraticHessian
public import PaperP1.Algebra.HomogeneousFactorDegrees
public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # A nonzero actual three-by-three Hessian minor proves quadratic irreducibility over any field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadricHessianIrreducibility

open MvPolynomial HomogeneousQuadraticHessian
open scoped Classical

variable {F : Type*} [Field F]

theorem first_coefficient (A : MvPolynomial (Fin 4) F) (i : Fin 4) :
    (pderiv i A).coeff 0 = A.coeff (Finsupp.single i 1) := by
  simp only [coeff_pderiv, zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]

theorem second_derivative_zero (A : MvPolynomial (Fin 4) F) (hA : A.IsHomogeneous 1)
    (i j : Fin 4) : pderiv j (pderiv i A) = 0 := by
  have hh : (pderiv i A).IsHomogeneous 0 := hA.pderiv
  rw [HomogeneousPolynomialEvaluation.homogeneous_zero_eq_C _ hh, pderiv_C]

theorem product_entry (A B : MvPolynomial (Fin 4) F)
    (hA : A.IsHomogeneous 1) (hB : B.IsHomogeneous 1) (i j : Fin 4) :
    entry (A * B) i j = A.coeff (Finsupp.single i 1) * B.coeff (Finsupp.single j 1) +
      B.coeff (Finsupp.single i 1) * A.coeff (Finsupp.single j 1) := by
  rw [entry, pderiv_mul, map_add, pderiv_mul, pderiv_mul,
    second_derivative_zero A hA, second_derivative_zero B hB, zero_mul, mul_zero,
    zero_add, add_zero]
  change constantCoeff (pderiv i A * pderiv j B + pderiv j A * pderiv i B) = _
  rw [map_add, map_mul, map_mul]
  change (pderiv i A).coeff 0 * (pderiv j B).coeff 0 +
    (pderiv j A).coeff 0 * (pderiv i B).coeff 0 = _
  rw [first_coefficient, first_coefficient, first_coefficient, first_coefficient]
  ring

theorem product_minor_zero (A B : MvPolynomial (Fin 4) F)
    (hA : A.IsHomogeneous 1) (hB : B.IsHomogeneous 1) (r c : Fin 3 → Fin 4) :
    Matrix.det (fun i j ↦ entry (A * B) (r i) (c j)) = 0 := by
  let a : Fin 4 → F := fun i ↦ A.coeff (Finsupp.single i 1)
  let b : Fin 4 → F := fun i ↦ B.coeff (Finsupp.single i 1)
  let L : Matrix (Fin 3) (Fin 2) F := fun i k ↦ if k = 0 then a (r i) else b (r i)
  let R : Matrix (Fin 2) (Fin 3) F := fun k j ↦ if k = 0 then b (c j) else a (c j)
  let M : Matrix (Fin 3) (Fin 3) F := fun i j ↦ entry (A * B) (r i) (c j)
  have he : M = L * R := by
    ext i j
    change entry (A * B) (r i) (c j) = (L * R) i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [L, R, a, b, product_entry A B hA hB]
  change M.det = 0
  by_contra hn
  have hfull : M.rank = 3 := Matrix.rank_of_det_ne_zero hn
  have hsmall : M.rank ≤ 2 := by
    rw [he]
    exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)
  omega

theorem zero_degree_unit (A : MvPolynomial (Fin 4) F) (hA : A ≠ 0) (hd : A.totalDegree = 0) :
    IsUnit A := by
  have he : A = C (A.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : A.coeff 0 ≠ 0 := by
    intro hz
    apply hA
    rw [he, hz, map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem irreducible_of_nonzero_minor (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2)
    (r c : Fin 3 → Fin 4) (hminor : Matrix.det (fun i j ↦ entry P (r i) (c j)) ≠ 0) :
    Irreducible P := by
  have hP0 : P ≠ 0 := by
    intro hz
    apply hminor
    have he : (fun i j : Fin 3 ↦ entry P (r i) (c j)) = (0 : Matrix (Fin 3) (Fin 3) F) := by
      ext i j
      simp [hz, entry]
    rw [he, Matrix.det_zero]
  have hd : P.totalDegree = 2 := hP.totalDegree hP0
  refine ⟨?_, ?_⟩
  · intro hu
    have hh := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B he
    by_cases huA : IsUnit A
    · exact Or.inl huA
    by_cases huB : IsUnit B
    · exact Or.inr huB
    have hAB : A * B ≠ 0 := by rw [← he]; exact hP0
    have hA0 : A ≠ 0 := left_ne_zero_of_mul hAB
    have hB0 : B ≠ 0 := right_ne_zero_of_mul hAB
    have hApos : 0 < A.totalDegree := by
      by_contra hn
      exact huA (zero_degree_unit A hA0 (Nat.eq_zero_of_not_pos hn))
    have hBpos : 0 < B.totalDegree := by
      by_contra hn
      exact huB (zero_degree_unit B hB0 (Nat.eq_zero_of_not_pos hn))
    have hsum : A.totalDegree + B.totalDegree = 2 := by
      rw [← totalDegree_mul_of_isDomain hA0 hB0, ← he, hd]
    have hAd : A.totalDegree = 1 := by omega
    have hBd : B.totalDegree = 1 := by omega
    obtain ⟨hAh, hBh⟩ := HomogeneousFactorDegrees.homogeneous_factors A B hAB 2 (he ▸ hP)
    rw [hAd] at hAh
    rw [hBd] at hBh
    exact False.elim (hminor (he ▸ product_minor_zero A B hAh hBh r c))

end PaperP1.QuadricHessianIrreducibility
