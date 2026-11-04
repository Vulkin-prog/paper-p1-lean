module

public import PaperP1.Asymptotics.DeterminantAuxiliaryHeight
public import PaperP1.Algebra.BivariateEvaluation
public import PaperP1.Algebra.PolynomialHeightArithmetic

/-! # The actual nonzero integer auxiliary polynomial on the full source population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantAuxiliaryPolynomial

open Finset Polynomial PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntegerRows
  PaperP1.DeterminantAuxiliaryCoefficients PaperP1.BiquadraticCoefficientPolynomials
  PaperP1.BivariateDegrees PaperP1.BivariateEvaluation

theorem rectangle_ne_zero (A B : ℕ) (w : Exponent A B → ℤ) (hw : w ≠ 0) : rectangle A B w ≠ 0 := by
  intro hf
  apply hw
  funext i
  have hc := congrArg (fun F : ℤ[X][X] ↦ (F.coeff i.2.val).coeff i.1.val) hf
  simpa only [rectangle_coefficient, coeff_zero, Pi.zero_apply] using hc

theorem rectangle_height_le (A B H : ℕ) (w : Exponent A B → ℤ) (hw : ∀ i, |w i| ≤ (H : ℤ)) :
    BivariateHeight.height (rectangle A B w) ≤ H := by
  apply PolynomialHeightArithmetic.bivariate_height_le
  intro b a
  have hh := rectangle_height A B w (H : ℤ) (Nat.cast_nonneg H) hw a b
  rw [← Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem exists_auxiliary (A B X : ℕ) (S : Finset Quad)
    (hbox : ∀ p ∈ S, p.1.1 ≤ X ∧ p.1.2 ≤ X ∧ p.2.1 ≤ X ∧ p.2.2 ≤ X)
    (he : ∀ p ∈ S, 0 < p.1.2) (hu : ∀ p ∈ S, 0 < p.2.1)
    (hsmall : ∀ P : Exponent A B → S,
      |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
        (∏ i, denominator A B (P i).val) < 1) :
    ∃ F : ℤ[X][X], F ≠ 0 ∧ degreeX F ≤ A ∧ degreeY F ≤ B ∧
      BivariateHeight.height F ≤ heightBound A B X ∧
        ∀ p ∈ S, evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) F = 0 := by
  obtain ⟨w, hw0, hw, hzero⟩ := exists_coefficients A B X S hbox he hu hsmall
  refine ⟨rectangle A B w, rectangle_ne_zero A B w hw0, rectangle_degreeX A B w,
    rectangle_degreeY A B w, rectangle_height_le A B _ w hw, ?_⟩
  intro p hp
  rw [rectangle_evaluation]
  simpa only [rationalEntry, mul_assoc] using hzero p hp

theorem uniform_auxiliary (A B Q : ℕ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset Quad,
      (∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N) →
      (∀ p ∈ S, 0 < p.1.2) → (∀ p ∈ S, 0 < p.2.1) →
      (∀ P : Exponent A B → S,
        |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
          (∏ i, denominator A B (P i).val) < 1) →
      ∃ F : ℤ[X][X], F ≠ 0 ∧ degreeX F ≤ A ∧ degreeY F ≤ B ∧
        BivariateHeight.height F ≤ N ^ κ ∧
          ∀ p ∈ S, evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) F = 0 := by
  obtain ⟨κ, N₀, h⟩ := DeterminantAuxiliaryHeight.uniform_coefficients A B Q
  refine ⟨κ, N₀, ?_⟩
  intro N hN S hbox he hu hsmall
  obtain ⟨w, hw0, hw, hzero⟩ := h N hN S hbox he hu hsmall
  refine ⟨rectangle A B w, rectangle_ne_zero A B w hw0, rectangle_degreeX A B w,
    rectangle_degreeY A B w, rectangle_height_le A B _ w hw, ?_⟩
  intro p hp
  rw [rectangle_evaluation]
  simpa only [rationalEntry, mul_assoc] using hzero p hp

end PaperP1.DeterminantAuxiliaryPolynomial
