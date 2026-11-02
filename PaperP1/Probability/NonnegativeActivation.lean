module

public import PaperP1.Probability.ActivePairCount
public import Mathlib.Tactic.FieldSimp

/-! # A linear truncation converts a relative second moment into an activation bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonnegativeActivation

open PaperP1.Algebra PaperP1.Probability

variable {Ω : Type*} [Fintype Ω]

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem truncation (P : FiniteProbability Ω) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (R : ℝ) (hR : 0 < R) :
    finiteExpectation P.weight X ≤
      R * finiteExpectation P.weight (fun ω ↦ if 0 < X ω then 1 else 0) +
        finiteExpectation P.weight (fun ω ↦ X ω ^ 2) / R := by
  have hpoint (ω : Ω) : X ω ≤ R * (if 0 < X ω then 1 else 0) + X ω ^ 2 / R := by
    have ht : 0 ≤ X ω ^ 2 / R := div_nonneg (sq_nonneg _) hR.le
    by_cases hx : 0 < X ω
    · rw [ite_eq_left hx, mul_one]
      by_cases hr : X ω ≤ R
      · linarith only [hr, ht]
      · have hq : X ω ≤ X ω ^ 2 / R := by
          apply (le_div_iff₀ hR).mpr
          nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hr) (hX ω)]
        linarith only [hq, hR]
    · rw [ite_eq_right hx, mul_zero, zero_add]
      have hz : X ω = 0 := le_antisymm (not_lt.mp hx) (hX ω)
      simpa only [hz] using ht
  have hb := finiteExpectation_mono P hpoint
  rw [finiteExpectation_add, finiteExpectation_const_mul] at hb
  have heq : finiteExpectation P.weight (fun ω ↦ X ω ^ 2 / R) =
      finiteExpectation P.weight (fun ω ↦ X ω ^ 2) / R := by
    simpa only [div_eq_mul_inv] using finiteExpectation_mul_const P.weight (fun ω ↦ X ω ^ 2) R⁻¹
  rwa [heq] at hb

theorem relative_second_bound (P : FiniteProbability Ω) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (B : ℝ) (hB : 0 < B)
    (hsecond : finiteExpectation P.weight (fun ω ↦ X ω ^ 2) ≤ B * finiteExpectation P.weight X) :
    finiteExpectation P.weight X ≤ 4 * B * finiteExpectation P.weight (fun ω ↦ if 0 < X ω then 1 else 0) := by
  have ht := truncation P X hX (2 * B) (by positivity)
  have htail : finiteExpectation P.weight (fun ω ↦ X ω ^ 2) / (2 * B) ≤ finiteExpectation P.weight X / 2 := by
    calc
      _ ≤ (B * finiteExpectation P.weight X) / (2 * B) := div_le_div_of_nonneg_right hsecond (by positivity)
      _ = _ := by field_simp
  linarith only [ht, htail]

end PaperP1.NonnegativeActivation
