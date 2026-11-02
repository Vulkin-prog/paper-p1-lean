module

public import PaperP1.Arithmetic.BiquadraticFormalNumerator
public import PaperP1.Arithmetic.BiquadraticCoefficientPolynomials

/-! # The actual bounded integer coefficient polynomials and formal cancellation are constructed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticAuxiliaryConstruction

open PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.BiquadraticFormalNumerator

theorem exists_auxiliary {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ ((B + 1) ^ (266 * q) : ℕ)) ∧
      (∃ χ : Fin 4, family w χ ≠ 0) ∧
      (∀ χ : Fin 4, BivariateDegrees.degreeX (family w χ) ≤ 3 * q - blockRank r χ ∧
        BivariateDegrees.degreeY (family w χ) ≤ 3 * q - blockRank s χ) ∧
      (∀ (χ : Fin 4) (a b : ℕ), |((family w χ).coeff b).coeff a| ≤ ((B + 1) ^ (266 * q) : ℕ)) ∧
      ∀ a b : ℕ, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0 := by
  obtain ⟨w, hne, hheight, hzero⟩ := exists_vanishing_numerator B hq hqB hr hs γ δ hγ hδ
  refine ⟨w, hne, hheight, family_nonzero w hne, family_degrees w, ?_, hzero⟩
  intro χ a b
  exact family_height w _ (by positivity) hheight χ a b

end PaperP1.BiquadraticAuxiliaryConstruction
