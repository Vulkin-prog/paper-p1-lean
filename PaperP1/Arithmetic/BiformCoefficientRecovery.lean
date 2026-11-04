module

public import PaperP1.Arithmetic.DeterminantAuxiliaryBiform

/-! # Exact recovery of all original integer coefficients from the projective biform -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiformCoefficientRecovery

open PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
  PaperP1.BiquadraticCoefficientPolynomials

theorem coefficient_recovery (A B : ℕ) (w : Exponent A B → ℤ)
    (a : Fin (A + 1)) (b : Fin (B + 1)) :
    ((biform A B w).coeff (fun₀ | 0 => a.val | 1 => A - a.val)).coeff
      (fun₀ | 0 => b.val | 1 => B - b.val) = w (a, b) := by
  have ha : a.val ≤ A := by have := a.isLt; omega
  have hb : b.val ≤ B := by have := b.isLt; omega
  have hout : (biform A B w).coeff (fun₀ | 0 => a.val | 1 => A - a.val) = forms A B w a := by
    unfold biform
    simp [Polynomial.coeff_homogenize, Nat.add_sub_of_le ha, outer_coefficient]
  rw [hout]
  unfold forms
  simp [Polynomial.coeff_homogenize, Nat.add_sub_of_le hb, row_coefficient]

theorem biform_zero_iff (A B : ℕ) (w : Exponent A B → ℤ) : biform A B w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    funext i
    have hc := coefficient_recovery A B w i.1 i.2
    rw [hw] at hc
    simpa using hc.symm
  · intro hw
    subst w
    simp [biform, outerPolynomial, forms, row]

theorem coefficient_bound_from_biform (A B H : ℕ) (w : Exponent A B → ℤ)
    (hheight : ∀ m n, |((biform A B w).coeff m).coeff n| ≤ (H : ℤ)) :
    ∀ i, |w i| ≤ (H : ℤ) := by
  intro i
  rw [← coefficient_recovery A B w i.1 i.2]
  exact hheight _ _

end PaperP1.BiformCoefficientRecovery
