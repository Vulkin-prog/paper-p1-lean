module

public import PaperP1.Model.JointBranchingBudget
public import PaperP1.Probability.BranchingTuples
public import PaperP1.Model.FactorialCountMoments

/-! # Finite actual factorial-moment recurrences from deterministic branching exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialBranching

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.FactorialCountMoments PaperP1.BranchingTuples
  PaperP1.JointBranchingBudget PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget

theorem factorial_zero (N L : ℕ) : factorialCountMoment (dyadicBlock N) L 0 = 1 := by
  simp [factorialCountMoment]

theorem factorial_succ_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (r : ℕ) (D : ℝ)
    (hD : ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      ((badStarts N L (rawValues A L)).card : ℝ) ≤ D) :
    factorialCountMoment (dyadicBlock N) L (r + 1) ≤
      ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D) * factorialCountMoment (dyadicBlock N) L r := by
  rw [← sum_tuple_joint_moments (subset_refl _) (r + 1), ← sum_tuple_joint_moments (subset_refl _) r]
  apply sum_tuple_succ_le (dyadicBlock N) r (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
    ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D)
  intro A hA hcard
  exact (sum_extensions_bound hN hL hA).trans (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (hD A hA hcard)) (infiniteJointMoment_nonneg L A))

theorem factorial_le_power {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (k : ℕ) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ r < k, ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      ((badStarts N L (rawValues A L)).card : ℝ) ≤ D) :
    factorialCountMoment (dyadicBlock N) L k ≤ ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D) ^ k := by
  have hM : 0 ≤ (N : ℝ) * (2 ^ L : ℝ)⁻¹ + D := by positivity
  have hbound : ∀ r : ℕ, r ≤ k → factorialCountMoment (dyadicBlock N) L r ≤
      ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D) ^ r := by
    intro r
    induction r with
    | zero => intro _; rw [factorial_zero, pow_zero]
    | succ r ih =>
      intro hr
      have hrec := factorial_succ_bound hN hL r D (hD r (by omega))
      have hprev := ih (by omega)
      calc
        _ ≤ ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D) * factorialCountMoment (dyadicBlock N) L r := hrec
        _ ≤ ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + D) ^ r :=
          mul_le_mul_of_nonneg_left hprev hM
        _ = _ := by rw [pow_succ]; ring
  exact hbound k le_rfl

end PaperP1.FactorialBranching
