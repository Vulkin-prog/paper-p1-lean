module

public import PaperP1.Algebra.GradedVeronesePieceEquiv
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # The actual Veronese Hilbert polynomial and its multiplicity under degree rescaling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseHilbertPolynomial

open Polynomial

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
variable (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ)

def rescale (p : ℚ[X]) : ℚ[X] := p.comp (C (D : ℚ) * X)

theorem rescale_eval (p : ℚ[X]) (n : ℕ) :
    (rescale D p).eval (n : ℚ) = p.eval ((n * D : ℕ) : ℚ) := by
  simp only [rescale, eval_comp, eval_mul, eval_C, eval_X, Nat.cast_mul]
  rw [mul_comm]

theorem isHilbertPolynomial {p : ℚ[X]}
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p) (hD : 0 < D) :
    GradedHilbertPolynomial.IsHilbertPolynomial (GradedVeroneseGrading.piece G D) (rescale D p) := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [rescale_eval, hN (n * D) (hn.trans (Nat.le_mul_of_pos_right n hD)),
    GradedVeronesePieceEquiv.finrank_eq]

theorem rescale_natDegree (p : ℚ[X]) (hD : 0 < D) : (rescale D p).natDegree = p.natDegree := by
  rw [rescale, natDegree_comp, natDegree_C_mul_X (D : ℚ) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)), mul_one]

theorem rescale_leadingCoeff (p : ℚ[X]) (hD : 0 < D) :
    (rescale D p).leadingCoeff = p.leadingCoeff * (D : ℚ) ^ p.natDegree := by
  rw [rescale, leadingCoeff_comp (by
    rw [natDegree_C_mul_X (D : ℚ) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD))]
    exact one_ne_zero), leadingCoeff_C_mul_X]

theorem exists_polynomial (h : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial G p) (hD : 0 < D) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (GradedVeroneseGrading.piece G D) p :=
  ⟨rescale D h.choose, isHilbertPolynomial G D h.choose_spec hD⟩

theorem multiplicity (h : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial G p) (hD : 0 < D) :
    GradedHilbertPolynomial.multiplicity (GradedVeroneseGrading.piece G D)
      (exists_polynomial G D h hD) = GradedHilbertPolynomial.multiplicity G h *
        (D : ℚ) ^ (GradedHilbertPolynomial.polynomial G h).natDegree := by
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ (isHilbertPolynomial G D h.choose_spec hD),
    rescale_natDegree D h.choose hD, rescale_leadingCoeff D h.choose hD]
  change (h.choose.natDegree.factorial : ℚ) * (h.choose.leadingCoeff * (D : ℚ) ^ h.choose.natDegree) =
    ((h.choose.natDegree.factorial : ℚ) * h.choose.leadingCoeff) * (D : ℚ) ^ h.choose.natDegree
  exact (mul_assoc _ _ _).symm

end PaperP1.GradedVeroneseHilbertPolynomial
