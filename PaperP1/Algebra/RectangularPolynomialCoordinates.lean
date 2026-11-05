module

public import PaperP1.Algebra.BivariateCurveDegreeTransport
public import PaperP1.Algebra.PolynomialHeightArithmetic

/-! # Exact rectangular monomial coordinates over the coefficient ring

These coordinates keep a positive-dimensional family of multiples available
when a degree bound is enlarged for interpolation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RectangularPolynomialCoordinates

open Polynomial Finset

abbrev Index (D : ℕ) := Fin (D + 1) × Fin (D + 1)

variable {R : Type*} [CommRing R]

def polynomial (D : ℕ) (w : Index D → R) : R[X][X] :=
  ∑ i, Polynomial.monomial i.2.val (Polynomial.monomial i.1.val (w i))

def polynomialLinear (D : ℕ) : (Index D → R) →ₗ[R] R[X][X] where
  toFun := polynomial D
  map_add' w v := by
    simp only [polynomial, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [polynomial, Pi.smul_apply, Finset.smul_sum, Polynomial.smul_monomial,
      RingHom.id_apply]

theorem coefficient_formula (D : ℕ) (w : Index D → R) (x y : ℕ) :
    ((polynomial D w).coeff y).coeff x =
      ∑ i : Index D, if i.2.val = y ∧ i.1.val = x then w i else 0 := by
  classical
  simp only [polynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hy : i.2.val = y <;> by_cases hx : i.1.val = x <;>
    simp only [Polynomial.coeff_monomial, hy, hx, ite_true, ite_false, and_self,
      false_and, and_false, Polynomial.coeff_zero]

theorem coefficient (D : ℕ) (w : Index D → R) (j : Index D) :
    ((polynomial D w).coeff j.2.val).coeff j.1.val = w j := by
  classical
  rw [coefficient_formula]
  have he (i : Index D) : (i.2.val = j.2.val ∧ i.1.val = j.1.val) ↔ i = j := by
    constructor
    · intro h
      exact Prod.ext (Fin.ext h.2) (Fin.ext h.1)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp_rw [he]
  simp

theorem coefficient_zero_of_outside (D : ℕ) (w : Index D → R) (x y : ℕ)
    (hxy : D < x ∨ D < y) : ((polynomial D w).coeff y).coeff x = 0 := by
  classical
  rw [coefficient_formula]
  apply Finset.sum_eq_zero
  intro i _
  have hn : ¬(i.2.val = y ∧ i.1.val = x) := by
    intro h
    have hx := i.1.isLt
    have hy := i.2.isLt
    omega
  exact ite_eq_right_iff.mpr (fun h ↦ (hn h).elim)

theorem polynomial_injective (D : ℕ) : Function.Injective (polynomial D : (Index D → R) → R[X][X]) := by
  intro w v h
  funext i
  simpa only [coefficient] using congrArg (fun P : R[X][X] ↦ (P.coeff i.2.val).coeff i.1.val) h

def coefficientsLinear (D : ℕ) : R[X][X] →ₗ[R] (Index D → R) where
  toFun P i := (P.coeff i.2.val).coeff i.1.val
  map_add' P Q := by ext i; simp only [Polynomial.coeff_add, Pi.add_apply]
  map_smul' c P := by ext i; simp only [Polynomial.coeff_smul, Pi.smul_apply, RingHom.id_apply]

theorem coefficients_polynomial (D : ℕ) (w : Index D → R) :
    coefficientsLinear D (polynomial D w) = w := by
  funext i
  exact coefficient D w i

theorem outer_degree_le (D : ℕ) (w : Index D → R) : (polynomial D w).natDegree ≤ D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro y hy
  apply Polynomial.ext
  intro x
  simpa only [Polynomial.coeff_zero] using coefficient_zero_of_outside D w x y (Or.inr hy)

theorem inner_degree_le (D : ℕ) (w : Index D → R) (y : ℕ) :
    ((polynomial D w).coeff y).natDegree ≤ D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro x hx
  exact coefficient_zero_of_outside D w x y (Or.inl hx)

theorem total_degree_le (D : ℕ) (w : Index D → R) :
    PlaneCurvePointCount.degree (polynomial D w) ≤ 2 * D := by
  apply Finset.sup_le
  intro y hy
  have houter := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hy)).trans
    (outer_degree_le D w)
  have hinner := inner_degree_le D w y
  omega

theorem reconstruction (D : ℕ) (P : R[X][X]) (houter : P.natDegree ≤ D)
    (hinner : ∀ y, (P.coeff y).natDegree ≤ D) :
    polynomial D (coefficientsLinear D P) = P := by
  ext y x
  by_cases hy : y ≤ D
  · by_cases hx : x ≤ D
    · let i : Index D := (⟨x, by omega⟩, ⟨y, by omega⟩)
      exact coefficient D _ i
    · rw [coefficient_zero_of_outside D _ x y (Or.inl (by omega))]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt ((hinner y).trans_lt (by omega))).symm
  · rw [coefficient_zero_of_outside D _ x y (Or.inr (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (houter.trans_lt (by omega)), Polynomial.coeff_zero]

theorem evaluation (D : ℕ) (w : Index D → R) (x y : R) :
    (polynomial D w).evalEval x y = ∑ i : Index D, w i * x ^ i.1.val * y ^ i.2.val := by
  rw [polynomial, Polynomial.evalEval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Polynomial.evalEval, Polynomial.eval_monomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]

theorem height_le (D H : ℕ) (w : Index D → ℤ) (hw : ∀ i, (w i).natAbs ≤ H) :
    BivariateHeight.height (polynomial D w) ≤ H := by
  classical
  apply PolynomialHeightArithmetic.bivariate_height_le
  intro y x
  by_cases hxy : x ≤ D ∧ y ≤ D
  · let i : Index D := (⟨x, by omega⟩, ⟨y, by omega⟩)
    have hc := coefficient D w i
    change (((polynomial D w).coeff i.2.val).coeff i.1.val).natAbs ≤ H
    rw [hc]
    exact hw i
  · rw [coefficient_zero_of_outside D w x y (by omega), Int.natAbs_zero]
    exact Nat.zero_le _

end PaperP1.RectangularPolynomialCoordinates
