module

public import PaperP1.Arithmetic.BiformCoefficientRecovery
public import Mathlib.Data.Fin.Rev

/-! # Exact coefficient and height preserving reversal of both projective coordinate pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantCoordinateFlip

open Finset PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
  PaperP1.BiformCoefficientRecovery PaperP1.TwoKernelDeterminantBoxes

def coordinateFlip (p : Quad) : Quad := ((p.1.2, p.1.1), (p.2.2, p.2.1))

def reverseExponent (A B : ℕ) : Equiv.Perm (Exponent A B) :=
  Equiv.prodCongr Fin.revPerm Fin.revPerm

def reverseCoefficients (A B : ℕ) (w : Exponent A B → ℤ) : Exponent A B → ℤ :=
  fun i ↦ w (reverseExponent A B i)

theorem coordinateFlip_involutive : Function.Involutive coordinateFlip := by
  intro p
  rfl

theorem coordinateFlip_injective : Function.Injective coordinateFlip := coordinateFlip_involutive.injective

theorem reverseExponent_involutive (A B : ℕ) : Function.Involutive (reverseExponent A B) := by
  rintro ⟨a, b⟩
  change (a.rev.rev, b.rev.rev) = (a, b)
  rw [Fin.rev_rev, Fin.rev_rev]

theorem reverseCoefficients_involutive (A B : ℕ) : Function.Involutive (reverseCoefficients A B) := by
  intro w
  funext i
  exact congrArg w (reverseExponent_involutive A B i)

theorem reverseCoefficients_nonzero (A B : ℕ) (w : Exponent A B → ℤ) (hw : w ≠ 0) :
    reverseCoefficients A B w ≠ 0 := by
  intro hz
  apply hw
  have h := congrArg (reverseCoefficients A B) hz
  rw [reverseCoefficients_involutive] at h
  exact h

theorem integerEntry_flip (A B : ℕ) (p : Quad) (i : Exponent A B) :
    integerEntry A B (coordinateFlip p) i = integerEntry A B p (reverseExponent A B i) := by
  have ha : (reverseExponent A B i).1.val = A - i.1.val := by
    simp [reverseExponent, Fin.val_rev, Nat.add_sub_add_right]
  have hb : (reverseExponent A B i).2.val = B - i.2.val := by
    simp [reverseExponent, Fin.val_rev, Nat.add_sub_add_right]
  have ha' : A - (A - i.1.val) = i.1.val := Nat.sub_sub_self (by have := i.1.isLt; omega)
  have hb' : B - (B - i.2.val) = i.2.val := Nat.sub_sub_self (by have := i.2.isLt; omega)
  simp only [integerEntry, coordinateFlip, ha, hb, ha', hb']
  push_cast
  ring

theorem biform_evaluation_flip (A B : ℕ) (w : Exponent A B → ℤ) (p : Quad) :
    MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2]
        (biform A B (reverseCoefficients A B w)) =
      MvPolynomial.eval₂ (MvPolynomial.eval ![((coordinateFlip p).2.2 : ℤ), (coordinateFlip p).2.1])
        ![((coordinateFlip p).1.1 : ℤ), (coordinateFlip p).1.2] (biform A B w) := by
  rw [biform_eval_original, original_integer_rows, biform_eval_original, original_integer_rows]
  calc
    _ = ∑ i : Exponent A B, integerEntry A B p (reverseExponent A B i) * w i := by
      exact Fintype.sum_equiv (reverseExponent A B) _ _ (fun i ↦ by
        simp only [reverseCoefficients, reverseExponent_involutive A B i])
    _ = _ := by simp_rw [← integerEntry_flip]

theorem reverse_biform_nonzero (A B : ℕ) (w : Exponent A B → ℤ) (hw : biform A B w ≠ 0) :
    biform A B (reverseCoefficients A B w) ≠ 0 := by
  apply biform_nonzero
  apply reverseCoefficients_nonzero
  exact fun h ↦ hw ((biform_zero_iff A B w).mpr h)

theorem reverse_biform_height (A B H : ℕ) (w : Exponent A B → ℤ)
    (hw : ∀ m n, |((biform A B w).coeff m).coeff n| ≤ (H : ℤ)) :
    ∀ m n, |((biform A B (reverseCoefficients A B w)).coeff m).coeff n| ≤ (H : ℤ) := by
  have hcoeff := coefficient_bound_from_biform A B H w hw
  exact biform_coefficient_bound A B H _ (fun i ↦ hcoeff (reverseExponent A B i))

end PaperP1.DeterminantCoordinateFlip
