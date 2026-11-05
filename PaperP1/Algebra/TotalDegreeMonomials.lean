module

public import PaperP1.Algebra.BivariateCurveDegreeTransport
public import PaperP1.Algebra.PolynomialHeightArithmetic

/-! # Exact triangular monomial coordinates for bounded total-degree integer polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TotalDegreeMonomials

open Polynomial Finset

abbrev Index (D : ℕ) := {i : Fin (D + 1) × Fin (D + 1) // i.1.val + i.2.val ≤ D}

def polynomial (D : ℕ) (w : Index D → ℤ) : ℤ[X][X] :=
  ∑ i, Polynomial.monomial i.val.2.val (Polynomial.monomial i.val.1.val (w i))

theorem index_card_pos (D : ℕ) : 0 < Fintype.card (Index D) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(⟨0, by omega⟩, ⟨0, by omega⟩), by simp⟩⟩

theorem coefficient_formula (D : ℕ) (w : Index D → ℤ) (x y : ℕ) :
    ((polynomial D w).coeff y).coeff x =
      ∑ i : Index D, if i.val.2.val = y ∧ i.val.1.val = x then w i else 0 := by
  classical
  simp only [polynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hy : i.val.2.val = y <;> by_cases hx : i.val.1.val = x <;>
    simp only [Polynomial.coeff_monomial, hy, hx, ite_true, ite_false, and_self,
      false_and, and_false, Polynomial.coeff_zero]

theorem coefficient (D : ℕ) (w : Index D → ℤ) (j : Index D) :
    ((polynomial D w).coeff j.val.2.val).coeff j.val.1.val = w j := by
  classical
  rw [coefficient_formula]
  have he (i : Index D) : (i.val.2.val = j.val.2.val ∧ i.val.1.val = j.val.1.val) ↔ i = j := by
    constructor
    · intro h
      exact Subtype.ext (Prod.ext (Fin.ext h.2) (Fin.ext h.1))
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp_rw [he]
  simp

theorem coefficient_zero_of_total_lt (D : ℕ) (w : Index D → ℤ) (x y : ℕ) (hxy : D < x + y) :
    ((polynomial D w).coeff y).coeff x = 0 := by
  classical
  rw [coefficient_formula]
  apply Finset.sum_eq_zero
  intro i _
  have hn : ¬(i.val.2.val = y ∧ i.val.1.val = x) := by
    intro h
    have hi := i.property
    omega
  exact ite_eq_right_iff.mpr (fun h ↦ (hn h).elim)

theorem total_degree_le (D : ℕ) (w : Index D → ℤ) :
    PlaneCurvePointCount.degree (polynomial D w) ≤ D := by
  apply Finset.sup_le
  intro y hy
  have hrow : (polynomial D w).coeff y ≠ 0 := Polynomial.mem_support_iff.mp hy
  have hc : ((polynomial D w).coeff y).coeff ((polynomial D w).coeff y).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hrow
  by_contra h
  exact hc (coefficient_zero_of_total_lt D w _ y (by omega))

theorem ne_zero (D : ℕ) (w : Index D → ℤ) (hw : w ≠ 0) : polynomial D w ≠ 0 := by
  intro hz
  apply hw
  funext i
  have hc := congrArg (fun P : ℤ[X][X] ↦ (P.coeff i.val.2.val).coeff i.val.1.val) hz
  simpa only [coefficient, Polynomial.coeff_zero, Pi.zero_apply] using hc

theorem evaluation (D : ℕ) (w : Index D → ℤ) (x y : ℤ) :
    (polynomial D w).evalEval x y = ∑ i : Index D, w i * x ^ i.val.1.val * y ^ i.val.2.val := by
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
  by_cases hex : ∃ i : Index D, i.val.1.val = x ∧ i.val.2.val = y
  · obtain ⟨i, hx, hy⟩ := hex
    rw [← hx, ← hy, coefficient]
    exact hw i
  · have hc : ((polynomial D w).coeff y).coeff x = 0 := by
      rw [coefficient_formula]
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬(i.val.2.val = y ∧ i.val.1.val = x) := fun h ↦ hex ⟨i, h.2, h.1⟩
      exact ite_eq_right_iff.mpr (fun h ↦ (hn h).elim)
    simp only [hc, Int.natAbs_zero, Nat.zero_le]

theorem reconstruction (D : ℕ) (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ D) :
    polynomial D (fun i ↦ (P.coeff i.val.2.val).coeff i.val.1.val) = P := by
  classical
  ext y x
  by_cases hxy : x + y ≤ D
  · let i : Index D := ⟨(⟨x, by omega⟩, ⟨y, by omega⟩), hxy⟩
    exact coefficient D _ i
  · have hc : (P.coeff y).coeff x = 0 := by
      by_contra hn
      have hd := BivariateTotalDegree.coefficient_degree_le P x y hn
      change x + y ≤ PlaneCurvePointCount.degree P at hd
      omega
    rw [coefficient_zero_of_total_lt D _ x y (by omega), hc]

end PaperP1.TotalDegreeMonomials
