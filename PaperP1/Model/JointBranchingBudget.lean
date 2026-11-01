module

public import PaperP1.Model.JointBranchingEvents

/-! # A finite extension budget for actual joint probabilities, at every order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointBranchingBudget

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.JointBranchingEvents
  PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget

theorem sum_extensions_bound {N L : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hA : A ⊆ dyadicBlock N) :
    (∑ x ∈ dyadicBlock N, infiniteJointMoment L (insert x A)) ≤
      ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + (badStarts N L (rawValues A L)).card) * infiniteJointMoment L A := by
  classical
  let E := badStarts N L (rawValues A L)
  let p : ℝ := (2 ^ L : ℝ)⁻¹
  let q : ℝ := infiniteJointMoment L A
  have hp : 0 ≤ p := by unfold p; positivity
  have hq : 0 ≤ q := infiniteJointMoment_nonneg L A
  have hpoint : ∀ x ∈ dyadicBlock N, infiniteJointMoment L (insert x A) ≤ p * q + if x ∈ E then q else 0 := by
    intro x hx
    by_cases hE : x ∈ E
    · rw [ite_eq_left hE]
      have hle := infiniteJointMoment_antitone L (subset_insert x A)
      have hnonneg := mul_nonneg hp hq
      change infiniteJointMoment L (insert x A) ≤ q at hle
      linarith
    · rw [ite_eq_right hE, add_zero]
      exact (retained_joint_factor hN hL hA hx hE).le
  have hfilter : (dyadicBlock N).filter (fun x ↦ x ∈ E) = E := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨badStarts_subset N L (rawValues A L) h, h⟩⟩
  calc
    _ ≤ ∑ x ∈ dyadicBlock N, (p * q + if x ∈ E then q else 0) := sum_le_sum hpoint
    _ = ((N : ℝ) * p + E.card) * q := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, hfilter, sum_const, nsmul_eq_mul]
      have hcard : (dyadicBlock N).card = N := by simp only [dyadicBlock, Nat.card_Ico, two_mul, Nat.add_sub_cancel_left]
      rw [hcard]
      ring
    _ = _ := rfl

end PaperP1.JointBranchingBudget
