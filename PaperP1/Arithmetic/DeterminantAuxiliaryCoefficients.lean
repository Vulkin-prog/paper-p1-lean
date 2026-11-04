module

public import PaperP1.Algebra.FiniteRowKernel
public import PaperP1.Arithmetic.DeterminantIntegerRows

/-! # Bounded auxiliary coefficient vectors on the entire actual finite point family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantAuxiliaryCoefficients

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntegerRows

def heightBound (A B X : ℕ) : ℕ :=
  (3 * ((A + 1) * (B + 1)) * (X ^ (A + B) + 1)) ^ ((A + 1) * (B + 1) - 1)

theorem exists_coefficients (A B X : ℕ) (S : Finset Quad)
    (hbox : ∀ p ∈ S, p.1.1 ≤ X ∧ p.1.2 ≤ X ∧ p.2.1 ≤ X ∧ p.2.2 ≤ X)
    (he : ∀ p ∈ S, 0 < p.1.2) (hu : ∀ p ∈ S, 0 < p.2.1)
    (hsmall : ∀ P : Exponent A B → S,
      |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
        (∏ i, denominator A B (P i).val) < 1) :
    ∃ w : Exponent A B → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ (heightBound A B X : ℤ)) ∧
      ∀ p ∈ S, (∑ i, (w i : ℚ) * rationalEntry A B p i) = 0 := by
  classical
  have hcard : Fintype.card (Exponent A B) = (A + 1) * (B + 1) := by
    simp only [Exponent, Fintype.card_prod, Fintype.card_fin]
  have hminor (P : Exponent A B → S) :
      (Matrix.of (fun i j ↦ (integerEntry A B (P i).val j : ℚ))).det = 0 := by
    have hz := integer_det_zero_of_small A B (fun i ↦ (P i).val)
      (fun i ↦ he _ (P i).property) (fun i ↦ hu _ (P i).property) (hsmall P)
    have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hz
    rw [Int.cast_det, Int.cast_zero] at hcast
    exact hcast
  have hheight (p : S) (i : Exponent A B) : |integerEntry A B p.val i| ≤ ((X ^ (A + B) + 1 : ℕ) : ℤ) := by
    have hb := hbox p.val p.property
    have hh := entry_height A B X p.val hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 i
    have hh' : |integerEntry A B p.val i| ≤ ((X ^ (A + B) : ℕ) : ℤ) := by
      have hc : (((integerEntry A B p.val i).natAbs : ℕ) : ℤ) ≤ ((X ^ (A + B) : ℕ) : ℤ) := by exact_mod_cast hh
      simpa only [Int.natCast_natAbs] using hc
    exact hh'.trans (by exact_mod_cast Nat.le_succ (X ^ (A + B)))
  obtain ⟨w, hw0, hw, hzero⟩ := FiniteRowKernel.exists_integer_annihilator
    (X ^ (A + B) + 1) (by omega) (by rw [hcard]; positivity)
    (fun p : S ↦ integerEntry A B p.val) hheight hminor
  refine ⟨w, hw0, ?_, ?_⟩
  · intro i
    simpa only [hcard, heightBound] using hw i
  · intro p hp
    have hz : (∑ i, (integerEntry A B p i : ℚ) * (w i : ℚ)) = 0 := by
      exact_mod_cast hzero (⟨p, hp⟩ : S)
    have hf : (∑ i, (integerEntry A B p i : ℚ) * (w i : ℚ)) =
        denominator A B p * (∑ i, (w i : ℚ) * rationalEntry A B p i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [← entry_clearing A B p (he p hp) (hu p hp) i]
      ring
    rw [hf] at hz
    exact (mul_eq_zero.mp hz).resolve_left (denominator_pos A B p (he p hp) (hu p hp)).ne'

end PaperP1.DeterminantAuxiliaryCoefficients
