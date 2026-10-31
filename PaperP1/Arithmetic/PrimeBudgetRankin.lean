module

public import PaperP1.Arithmetic.SmoothSquarefreeCount
public import PaperP1.Arithmetic.LogarithmicPrimeBudget

/-! # Companion T22.3 with an explicit uniform logarithmic constant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeBudgetRankin

open Finset PaperP1.SmoothSquarefreeCount PaperP1.LogarithmicPrimeBudget

theorem card_values_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (X : ℝ) (hX : 0 ≤ X) (Y σ : ℝ) (hY : 1 < Y)
    (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3 / 4)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ Y) :
    ((values P X).card : ℝ) ≤
      X ^ σ * Real.exp (budgetConstant * Y ^ (1 - σ) / Real.log Y) := by
  calc
    _ ≤ X ^ σ * eulerProduct P σ := card_values_le_euler P (fun p hp ↦ (hP p hp).pos) X hX σ hσ
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (primeBudgetEuler_le P hP Y σ hY (by linarith) hσ3 hbudget) (Real.rpow_nonneg hX σ)

theorem log_values_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (X : ℝ) (hX : 1 ≤ X) (Y σ : ℝ) (hY : 1 < Y)
    (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3 / 4)
    (hbudget : (∑ p ∈ P, Real.log p) ≤ Y) :
    Real.log ((values P X).card : ℝ) ≤
      σ * Real.log X + budgetConstant * Y ^ (1 - σ) / Real.log Y := by
  have hXpos : 0 < X := by linarith
  have hcount : (0 : ℝ) < (values P X).card := by exact_mod_cast card_values_pos P X hX
  have h := Real.log_le_log hcount (card_values_le_exp P hP X hXpos.le Y σ hY hσ hσ3 hbudget)
  simpa only [Real.log_mul (Real.rpow_pos_of_pos hXpos σ).ne' (Real.exp_ne_zero _),
    Real.log_rpow hXpos, Real.log_exp] using h

theorem source_uniform_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ X Y σ : ℝ, 1 ≤ X → 3 ≤ Y → 3 / 5 ≤ σ → σ ≤ 3 / 4 →
        (∑ p ∈ P, Real.log p) ≤ Y →
          Real.log ((values P X).card : ℝ) ≤
            σ * Real.log X + C * (1 + Y ^ (1 - σ) / Real.log Y) := by
  refine ⟨budgetConstant, budgetConstant_pos, ?_⟩
  intro P hP X Y σ hX hY hσ hσ3 hbudget
  have h := log_values_le P hP X hX Y σ (by linarith) (by linarith) hσ3 hbudget
  have hC := budgetConstant_pos
  calc
    _ ≤ σ * Real.log X + budgetConstant * Y ^ (1 - σ) / Real.log Y := h
    _ ≤ _ := by
      rw [mul_add, mul_one, ← mul_div_assoc]
      linarith

/-- Both source conclusions, including the literal positive-integer zeta series. -/
theorem companion_T22_3 :
    (∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) → ∀ X σ : ℝ,
      0 ≤ X → 1 / 2 < σ → σ < 1 →
        ((values P X).card : ℝ) ≤ X ^ σ * PaperP1.PowerSeriesTail.total (2 * σ) * eulerProduct P σ) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ X Y σ : ℝ, 1 ≤ X → 3 ≤ Y → 3 / 5 ≤ σ → σ ≤ 3 / 4 →
        (∑ p ∈ P, Real.log p) ≤ Y →
          Real.log ((values P X).card : ℝ) ≤
            σ * Real.log X + C * (1 + Y ^ (1 - σ) / Real.log Y)) := by
  refine ⟨?_, source_uniform_log_bound⟩
  intro P hP X σ hX hσ _hσ1
  exact card_values_le_source_rankin P hP X hX σ hσ

end PaperP1.PrimeBudgetRankin
