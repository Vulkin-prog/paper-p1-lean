module

public import PaperP1.Arithmetic.BiquadraticRungeMatrix
public import PaperP1.Algebra.BivariateDegrees

/-! # Actual four integer coefficient polynomials with their exact partial degrees and heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticCoefficientPolynomials

open Finset Polynomial PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix

def row (m : ℕ) (w : Fin (m + 1) → ℤ) : ℤ[X] := ∑ a, monomial a.val (w a)

def rectangle (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ) : ℤ[X][X] :=
  ∑ b, monomial b.val (row m (fun a ↦ w (a, b)))

theorem row_coefficient (m : ℕ) (w : Fin (m + 1) → ℤ) (a : Fin (m + 1)) :
    (row m w).coeff a.val = w a := by
  classical
  simp [row, Polynomial.coeff_monomial, Fin.val_inj]

theorem row_degree (m : ℕ) (w : Fin (m + 1) → ℤ) : (row m w).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro a _
  exact (natDegree_monomial_le _).trans (by omega)

theorem rectangle_outer_coefficient (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ)
    (b : Fin (n + 1)) : (rectangle m n w).coeff b.val = row m (fun a ↦ w (a, b)) := by
  classical
  simp [rectangle, Polynomial.coeff_monomial, Fin.val_inj]

theorem rectangle_coefficient (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ)
    (a : Fin (m + 1)) (b : Fin (n + 1)) : ((rectangle m n w).coeff b.val).coeff a.val = w (a, b) := by
  rw [rectangle_outer_coefficient, row_coefficient]

theorem rectangle_degreeY (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ) :
    BivariateDegrees.degreeY (rectangle m n w) ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro b _
  exact (natDegree_monomial_le _).trans (by omega)

theorem rectangle_swap (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ) :
    Bivariate.swap (rectangle m n w) = rectangle n m (fun p ↦ w (p.2, p.1)) := by
  unfold rectangle row
  simp_rw [map_sum, Bivariate.swap_monomial_monomial]
  exact sum_comm

theorem rectangle_degreeX (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ) :
    BivariateDegrees.degreeX (rectangle m n w) ≤ m := by
  rw [BivariateDegrees.degreeX, rectangle_swap]
  exact rectangle_degreeY n m _

theorem rectangle_height (m n : ℕ) (w : Fin (m + 1) × Fin (n + 1) → ℤ) (H : ℤ) (hH : 0 ≤ H)
    (hw : ∀ p, |w p| ≤ H) (a b : ℕ) : |((rectangle m n w).coeff b).coeff a| ≤ H := by
  by_cases hb : b ≤ n
  · let b' : Fin (n + 1) := ⟨b, by omega⟩
    change |((rectangle m n w).coeff b'.val).coeff a| ≤ H
    rw [rectangle_outer_coefficient]
    by_cases ha : a ≤ m
    · let a' : Fin (m + 1) := ⟨a, by omega⟩
      change |(row m (fun a ↦ w (a, b'))).coeff a'.val| ≤ H
      rw [row_coefficient]
      exact hw (a', b')
    · rw [coeff_eq_zero_of_natDegree_lt ((row_degree m _).trans_lt (by omega))]
      exact hH
  · rw [coeff_eq_zero_of_natDegree_lt ((rectangle_degreeY m n w).trans_lt (by omega)), coeff_zero, abs_zero]
    exact hH

def family {q : ℕ} {r s : Fin 3 → ℕ} (w : CoefficientIndex q r s → ℤ) : Fin 4 → ℤ[X][X] :=
  Fin.cases (rectangle (3 * q) (3 * q) (fun p ↦ w (.inl p)))
    (fun j ↦ rectangle (3 * q - r j) (3 * q - s j) (fun p ↦ w (.inr ⟨j, p⟩)))

theorem family_degrees {q : ℕ} {r s : Fin 3 → ℕ} (w : CoefficientIndex q r s → ℤ) (χ : Fin 4) :
    BivariateDegrees.degreeX (family w χ) ≤ 3 * q - blockRank r χ ∧
      BivariateDegrees.degreeY (family w χ) ≤ 3 * q - blockRank s χ := by
  refine Fin.cases ?_ ?_ χ
  · change BivariateDegrees.degreeX (rectangle (3 * q) (3 * q) (fun p ↦ w (.inl p))) ≤ 3 * q ∧
      BivariateDegrees.degreeY (rectangle (3 * q) (3 * q) (fun p ↦ w (.inl p))) ≤ 3 * q
    exact ⟨rectangle_degreeX (3 * q) (3 * q) _, rectangle_degreeY (3 * q) (3 * q) _⟩
  · intro j
    change BivariateDegrees.degreeX (rectangle (3 * q - r j) (3 * q - s j) (fun p ↦ w (.inr ⟨j, p⟩))) ≤ 3 * q - r j ∧
      BivariateDegrees.degreeY (rectangle (3 * q - r j) (3 * q - s j) (fun p ↦ w (.inr ⟨j, p⟩))) ≤ 3 * q - s j
    exact ⟨rectangle_degreeX (3 * q - r j) (3 * q - s j) _, rectangle_degreeY (3 * q - r j) (3 * q - s j) _⟩

theorem family_height {q : ℕ} {r s : Fin 3 → ℕ} (w : CoefficientIndex q r s → ℤ)
    (H : ℤ) (hH : 0 ≤ H) (hw : ∀ i, |w i| ≤ H) (χ : Fin 4) (a b : ℕ) :
    |((family w χ).coeff b).coeff a| ≤ H := by
  refine Fin.cases ?_ ?_ χ
  · exact rectangle_height _ _ _ H hH (fun p ↦ hw (.inl p)) a b
  · intro j
    exact rectangle_height _ _ _ H hH (fun p ↦ hw (.inr ⟨j, p⟩)) a b

theorem family_nonzero {q : ℕ} {r s : Fin 3 → ℕ} (w : CoefficientIndex q r s → ℤ) (hw : w ≠ 0) :
    ∃ χ : Fin 4, family w χ ≠ 0 := by
  by_contra hn
  have hzero : ∀ χ : Fin 4, family w χ = 0 := fun χ ↦ by
    by_contra hχ
    exact hn ⟨χ, hχ⟩
  apply hw
  funext i
  rcases i with p | ⟨j, p⟩
  · have h := hzero 0
    change rectangle (3 * q) (3 * q) (fun p ↦ w (.inl p)) = 0 at h
    have hc := congrArg (fun P : ℤ[X][X] ↦ (P.coeff p.2.val).coeff p.1.val) h
    simpa only [rectangle_coefficient, coeff_zero, Pi.zero_apply] using hc
  · have h := hzero j.succ
    change rectangle (3 * q - r j) (3 * q - s j) (fun p ↦ w (.inr ⟨j, p⟩)) = 0 at h
    have hc := congrArg (fun P : ℤ[X][X] ↦ (P.coeff p.2.val).coeff p.1.val) h
    simpa only [rectangle_coefficient, coeff_zero, Pi.zero_apply] using hc

end PaperP1.BiquadraticCoefficientPolynomials
