module

public import PaperP1.Arithmetic.DeterminantAuxiliaryCoefficients

/-! # Fixed auxiliary degrees give an explicit coefficient exponent before the source height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantAuxiliaryHeight

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntegerRows
  PaperP1.DeterminantAuxiliaryCoefficients

theorem heightBound_le_power (A B Q N X : ℕ) (hN : 1 ≤ N) (hX : X ≤ Q * N)
    (hlarge : 3 * ((A + 1) * (B + 1)) * (Q ^ (A + B) + 1) ≤ N) :
    heightBound A B X ≤ N ^ ((A + B + 1) * ((A + 1) * (B + 1) - 1)) := by
  let d := A + B
  let H := (A + 1) * (B + 1)
  have hpow : X ^ d ≤ Q ^ d * N ^ d := by simpa only [mul_pow] using Nat.pow_le_pow_left hX d
  have hnPow : 1 ≤ N ^ d := one_le_pow₀ hN
  have hsum : X ^ d + 1 ≤ (Q ^ d + 1) * N ^ d := by nlinarith only [hpow, hnPow]
  have hbase : 3 * H * (X ^ d + 1) ≤ N ^ (d + 1) := by
    calc
      _ ≤ 3 * H * ((Q ^ d + 1) * N ^ d) := Nat.mul_le_mul_left _ hsum
      _ = (3 * H * (Q ^ d + 1)) * N ^ d := by ring
      _ ≤ N * N ^ d := Nat.mul_le_mul_right _ hlarge
      _ = _ := by rw [pow_succ]; ring
  change (3 * H * (X ^ d + 1)) ^ (H - 1) ≤ N ^ ((d + 1) * (H - 1))
  exact (Nat.pow_le_pow_left hbase (H - 1)).trans_eq (pow_mul N (d + 1) (H - 1)).symm

theorem uniform_coefficients (A B Q : ℕ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset Quad,
      (∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N) →
      (∀ p ∈ S, 0 < p.1.2) → (∀ p ∈ S, 0 < p.2.1) →
      (∀ P : Exponent A B → S,
        |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
          (∏ i, denominator A B (P i).val) < 1) →
      ∃ w : Exponent A B → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        ∀ p ∈ S, (∑ i, (w i : ℚ) * rationalEntry A B p i) = 0 := by
  let κ := (A + B + 1) * ((A + 1) * (B + 1) - 1)
  let N₀ := max 2 (3 * ((A + 1) * (B + 1)) * (Q ^ (A + B) + 1))
  refine ⟨κ, N₀, ?_⟩
  intro N hN S hbox he hu hsmall
  obtain ⟨w, hw0, hw, hzero⟩ := exists_coefficients A B (Q * N) S hbox he hu hsmall
  have hheight := heightBound_le_power A B Q N (Q * N) (by dsimp [N₀] at hN; omega) (le_refl _)
    (by dsimp [N₀] at hN; omega)
  refine ⟨w, hw0, ?_, hzero⟩
  intro i
  exact (hw i).trans (by exact_mod_cast hheight)

end PaperP1.DeterminantAuxiliaryHeight
