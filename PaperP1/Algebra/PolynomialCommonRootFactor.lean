module

public import Mathlib.Algebra.Polynomial.Div

/-! # The exact common power at a root leaves a nonzero value in at least one coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialCommonRootFactor

open Polynomial

theorem exists_factor {F : Type*} [Field F] (P Q : F[X]) (hne : P ≠ 0 ∨ Q ≠ 0) (x : F) :
    ∃ (m : ℕ) (A B : F[X]), P = (X - C x) ^ m * A ∧ Q = (X - C x) ^ m * B ∧
      (A.eval x ≠ 0 ∨ B.eval x ≠ 0) := by
  by_cases hP : P = 0
  · have hQ := hne.resolve_left (not_not.mpr hP)
    obtain ⟨B, hB, hBn⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ x
    refine ⟨rootMultiplicity x Q, 0, B, ?_, hB, Or.inr ?_⟩
    · simp only [hP, mul_zero]
    · intro hz
      exact hBn (dvd_iff_isRoot.mpr hz)
  · by_cases hQ : Q = 0
    · obtain ⟨A, hA, hAn⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP x
      refine ⟨rootMultiplicity x P, A, 0, hA, ?_, Or.inl ?_⟩
      · simp only [hQ, mul_zero]
      · intro hz
        exact hAn (dvd_iff_isRoot.mpr hz)
    · by_cases hle : rootMultiplicity x P ≤ rootMultiplicity x Q
      · obtain ⟨A, hA, hAn⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP x
        obtain ⟨B, hB⟩ := (le_rootMultiplicity_iff hQ).mp hle
        refine ⟨rootMultiplicity x P, A, B, hA, hB, Or.inl ?_⟩
        intro hz
        exact hAn (dvd_iff_isRoot.mpr hz)
      · have hle' : rootMultiplicity x Q ≤ rootMultiplicity x P := Nat.le_of_lt (Nat.lt_of_not_ge hle)
        obtain ⟨B, hB, hBn⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ x
        obtain ⟨A, hA⟩ := (le_rootMultiplicity_iff hP).mp hle'
        refine ⟨rootMultiplicity x Q, A, B, hA, hB, Or.inr ?_⟩
        intro hz
        exact hBn (dvd_iff_isRoot.mpr hz)

end PaperP1.PolynomialCommonRootFactor
