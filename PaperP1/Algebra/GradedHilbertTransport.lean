module

public import PaperP1.Algebra.GradedHilbertPolynomial

/-! # Actual Hilbert polynomials and multiplicities are invariant under equality of piece dimensions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedHilbertTransport

open PaperP1.GradedHilbertPolynomial

variable {F A B : Type*} [Field F] [AddCommGroup A] [AddCommGroup B] [Module F A] [Module F B]
  (G : ℕ → Submodule F A) (H : ℕ → Submodule F B)
  (h : ∀ n, Module.finrank F (G n) = Module.finrank F (H n))

include h in
theorem isHilbertPolynomial_iff (p : Polynomial ℚ) : IsHilbertPolynomial G p ↔ IsHilbertPolynomial H p := by
  constructor <;> rintro ⟨N, hN⟩ <;> refine ⟨N, fun n hn ↦ ?_⟩
  · rw [← h n]
    exact hN n hn
  · rw [h n]
    exact hN n hn

include h in
theorem exists_polynomial_iff : (∃ p, IsHilbertPolynomial G p) ↔ ∃ p, IsHilbertPolynomial H p :=
  exists_congr (isHilbertPolynomial_iff G H h)

include h in
theorem polynomial_eq (hG : ∃ p, IsHilbertPolynomial G p) (hH : ∃ p, IsHilbertPolynomial H p) :
    polynomial G hG = polynomial H hH := by
  apply GradedHilbertPolynomial.unique hG.choose_spec
  exact (isHilbertPolynomial_iff G H h _).mpr hH.choose_spec

include h in
theorem multiplicity_eq (hG : ∃ p, IsHilbertPolynomial G p) (hH : ∃ p, IsHilbertPolynomial H p) :
    multiplicity G hG = multiplicity H hH := by
  simp only [GradedHilbertPolynomial.multiplicity, polynomial_eq G H h hG hH]

end PaperP1.GradedHilbertTransport
