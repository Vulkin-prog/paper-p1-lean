module

public import PaperP1.Asymptotics.DeterminantAuxiliaryHeight

/-! # One coefficient-height exponent before all bounded degree choices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantBoundedAuxiliaryHeight

open Finset PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryCoefficients
  PaperP1.TwoKernelDeterminantBoxes

theorem heightBound_le_common_power (Amax A B Q N : ℕ) (hA : A ≤ Amax) (hQ : 1 ≤ Q)
    (hN : 1 ≤ N)
    (hlarge : 3 * ((Amax + 1) * (B + 1)) * (Q ^ (Amax + B) + 1) ≤ N) :
    heightBound A B (Q * N) ≤ N ^ ((Amax + B + 1) * ((Amax + 1) * (B + 1) - 1)) := by
  have hH : (A + 1) * (B + 1) ≤ (Amax + 1) * (B + 1) := Nat.mul_le_mul_right _ (by omega)
  have hq : Q ^ (A + B) + 1 ≤ Q ^ (Amax + B) + 1 :=
    Nat.add_le_add_right (Nat.pow_le_pow_right hQ (by omega)) 1
  have hbound : 3 * ((A + 1) * (B + 1)) * (Q ^ (A + B) + 1) ≤ N := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 3 hH) hq).trans hlarge
  have hexponent : (A + B + 1) * ((A + 1) * (B + 1) - 1) ≤
      (Amax + B + 1) * ((Amax + 1) * (B + 1) - 1) :=
    Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right hH 1)
  exact (DeterminantAuxiliaryHeight.heightBound_le_power A B Q N (Q * N) hN le_rfl hbound).trans
    (Nat.pow_le_pow_right hN hexponent)

theorem uniform_coefficients (Amax B Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ≤ Amax, ∀ S : Finset Quad,
      (∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N) →
      (∀ p ∈ S, 0 < p.1.2) → (∀ p ∈ S, 0 < p.2.1) →
      (∀ P : Exponent A B → S,
        |(rationalMatrix A B (fun i ↦ (P i).val)).det| *
          (∏ i, denominator A B (P i).val) < 1) →
      ∃ w : Exponent A B → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        ∀ p ∈ S, (∑ i, (w i : ℚ) * rationalEntry A B p i) = 0 := by
  let κ := (Amax + B + 1) * ((Amax + 1) * (B + 1) - 1)
  let N₀ := max 2 (3 * ((Amax + 1) * (B + 1)) * (Q ^ (Amax + B) + 1))
  refine ⟨κ, N₀, ?_⟩
  intro N hN A hA S hbox he hu hsmall
  obtain ⟨w, hw₀, hw, hzero⟩ := exists_coefficients A B (Q * N) S hbox he hu hsmall
  have hh := heightBound_le_common_power Amax A B Q N hA hQ
    (by dsimp [N₀] at hN; omega) (by dsimp [N₀] at hN; omega)
  exact ⟨w, hw₀, fun i ↦ (hw i).trans (by exact_mod_cast hh), hzero⟩

end PaperP1.DeterminantBoundedAuxiliaryHeight
