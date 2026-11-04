module

public import PaperP1.Arithmetic.DeterminantAuxiliaryPolynomial
public import PaperP1.Diophantine.BihomogeneousSwap

/-! # The bounded integer auxiliary equation on the actual two projective pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantAuxiliaryBiform

open Finset Polynomial PaperP1.DeterminantIntegerRows
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.HomogeneousCharts
  PaperP1.TwoKernelDeterminantBoxes

def forms (A B : ℕ) (w : Exponent A B → ℤ) (a : Fin (A + 1)) :
    MvPolynomial (Fin 2) ℤ := (row B (fun b ↦ w (a, b))).homogenize B

theorem forms_homogeneous (A B : ℕ) (w : Exponent A B → ℤ) (a : Fin (A + 1)) :
    (forms A B w a).IsHomogeneous B := Polynomial.isHomogeneous_homogenize _

theorem forms_chart (A B : ℕ) (w : Exponent A B → ℤ) (a : Fin (A + 1)) :
    chart (forms A B w a) = row B (fun b ↦ w (a, b)) := by
  exact Polynomial.aeval_homogenize_X_one _ (row_degree B _)

theorem forms_eval (A B : ℕ) (w : Exponent A B → ℤ) (a : Fin (A + 1))
    (z : Fin 2 → ℤ) :
    MvPolynomial.eval z (forms A B w a) =
      ∑ b : Fin (B + 1), w (a, b) * z 0 ^ b.val * z 1 ^ (B - b.val) := by
  rw [BihomogeneousSwap.eval_binary_expansion _ (forms_homogeneous A B w a), forms_chart]
  simp only [row_coefficient]

theorem forms_nonzero (A B : ℕ) (w : Exponent A B → ℤ) (hw : w ≠ 0) :
    ∃ a, forms A B w a ≠ 0 := by
  by_contra hn
  apply hw
  funext i
  have ha : forms A B w i.1 = 0 := not_not.mp ((not_exists.mp hn) i.1)
  have hc := congrArg (fun F : MvPolynomial (Fin 2) ℤ ↦ (chart F).coeff i.2.val) ha
  rw [forms_chart, row_coefficient] at hc
  simpa only [chart, map_zero, coeff_zero, Pi.zero_apply, Prod.mk.eta] using hc

def outerPolynomial (A B : ℕ) (w : Exponent A B → ℤ) :
    Polynomial (MvPolynomial (Fin 2) ℤ) := ∑ a, monomial a.val (forms A B w a)

theorem outer_degree (A B : ℕ) (w : Exponent A B → ℤ) :
    (outerPolynomial A B w).natDegree ≤ A := by
  apply natDegree_sum_le_of_forall_le
  intro a _
  exact (natDegree_monomial_le _).trans (by omega)

theorem outer_coefficient (A B : ℕ) (w : Exponent A B → ℤ) (a : Fin (A + 1)) :
    (outerPolynomial A B w).coeff a.val = forms A B w a := by
  classical
  simp [outerPolynomial, Polynomial.coeff_monomial, Fin.val_inj]

def biform (A B : ℕ) (w : Exponent A B → ℤ) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2) ℤ) := (outerPolynomial A B w).homogenize A

theorem biform_homogeneous (A B : ℕ) (w : Exponent A B → ℤ) :
    (biform A B w).IsHomogeneous A := Polynomial.isHomogeneous_homogenize _

theorem biform_chart (A B : ℕ) (w : Exponent A B → ℤ) :
    chart (biform A B w) = outerPolynomial A B w := by
  exact Polynomial.aeval_homogenize_X_one _ (outer_degree A B w)

theorem biform_chart_coefficient (A B : ℕ) (w : Exponent A B → ℤ) (a : Fin (A + 1)) :
    (chart (biform A B w)).coeff a.val = forms A B w a := by
  rw [biform_chart, outer_coefficient]

theorem biform_nonzero (A B : ℕ) (w : Exponent A B → ℤ) (hw : w ≠ 0) :
    biform A B w ≠ 0 := by
  obtain ⟨a, ha⟩ := forms_nonzero A B w hw
  intro hf
  have hc := congrArg (fun F : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) ℤ) ↦
    (chart F).coeff a.val) hf
  rw [biform_chart_coefficient] at hc
  exact ha (by simpa only [chart, map_zero, coeff_zero] using hc)

theorem biform_eval_original (A B : ℕ) (w : Exponent A B → ℤ) (v z : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval z) v (biform A B w) =
      BidegreeOneElimination.original (forms A B w) v z := by
  conv_lhs => rw [BihomogeneousSwap.binary_expansion _ (biform_homogeneous A B w)]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, biform_chart_coefficient, BidegreeOneElimination.original]

theorem original_integer_rows (A B : ℕ) (w : Exponent A B → ℤ) (p : Quad) :
    BidegreeOneElimination.original (forms A B w)
      ![(p.1.1 : ℤ), p.1.2] ![(p.2.2 : ℤ), p.2.1] =
        ∑ i, integerEntry A B p i * w i := by
  simp only [BidegreeOneElimination.original, forms_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [integerEntry, Nat.cast_mul, Nat.cast_pow]
  ring

theorem row_sum_clearing (A B : ℕ) (w : Exponent A B → ℤ) (p : Quad)
    (he : 0 < p.1.2) (hu : 0 < p.2.1) :
    ((∑ i, integerEntry A B p i * w i : ℤ) : ℚ) =
      denominator A B p * ∑ i, (w i : ℚ) * rationalEntry A B p i := by
  simp only [Int.cast_sum, Int.cast_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← entry_clearing A B p he hu i]
  ring

theorem biform_zero_of_rational_zero (A B : ℕ) (w : Exponent A B → ℤ) (p : Quad)
    (he : 0 < p.1.2) (hu : 0 < p.2.1)
    (hz : (∑ i, (w i : ℚ) * rationalEntry A B p i) = 0) :
    MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
      ![(p.1.1 : ℤ), p.1.2] (biform A B w) = 0 := by
  rw [biform_eval_original, original_integer_rows]
  have h := row_sum_clearing A B w p he hu
  rw [hz, mul_zero] at h
  exact_mod_cast h

theorem forms_coefficient_bound (A B H : ℕ) (w : Exponent A B → ℤ)
    (hw : ∀ i, |w i| ≤ (H : ℤ)) (a : Fin (A + 1)) (m : Fin 2 →₀ ℕ) :
    |(forms A B w a).coeff m| ≤ (H : ℤ) := by
  rw [forms, Polynomial.coeff_homogenize]
  split_ifs with hm
  · let b : Fin (B + 1) := ⟨m 0, by omega⟩
    change |(row B (fun b ↦ w (a, b))).coeff b.val| ≤ (H : ℤ)
    rw [row_coefficient]
    exact hw (a, b)
  · simpa only [abs_zero] using (Nat.cast_nonneg H : (0 : ℤ) ≤ H)

theorem biform_coefficient_bound (A B H : ℕ) (w : Exponent A B → ℤ)
    (hw : ∀ i, |w i| ≤ (H : ℤ)) (m n : Fin 2 →₀ ℕ) :
    |((biform A B w).coeff m).coeff n| ≤ (H : ℤ) := by
  rw [biform, Polynomial.coeff_homogenize]
  split_ifs with hm
  · let a : Fin (A + 1) := ⟨m 0, by omega⟩
    change |((outerPolynomial A B w).coeff a.val).coeff n| ≤ (H : ℤ)
    rw [outer_coefficient]
    exact forms_coefficient_bound A B H w hw a n
  · simp

theorem uniform_biform (A B Q : ℕ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset Quad,
      (∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N) →
      (∀ p ∈ S, 0 < p.1.2) → (∀ p ∈ S, 0 < p.2.1) →
      (∀ P : Exponent A B → S,
        |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
          (∏ i, denominator A B (P i).val) < 1) →
      ∃ w : Exponent A B → ℤ, biform A B w ≠ 0 ∧
        (biform A B w).IsHomogeneous A ∧ (∀ a, (forms A B w a).IsHomogeneous B) ∧
        (∀ m n, |((biform A B w).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        ∀ p ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
          ![(p.1.1 : ℤ), p.1.2] (biform A B w) = 0 := by
  obtain ⟨κ, N₀, h⟩ := DeterminantAuxiliaryHeight.uniform_coefficients A B Q
  refine ⟨κ, N₀, ?_⟩
  intro N hN S hbox he hu hsmall
  obtain ⟨w, hw0, hw, hzero⟩ := h N hN S hbox he hu hsmall
  exact ⟨w, biform_nonzero A B w hw0, biform_homogeneous A B w,
    forms_homogeneous A B w, biform_coefficient_bound A B (N ^ κ) w hw,
    fun p hp ↦ biform_zero_of_rational_zero A B w p (he p hp) (hu p hp) (hzero p hp)⟩

end PaperP1.DeterminantAuxiliaryBiform
