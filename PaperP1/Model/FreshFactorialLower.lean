module

public import PaperP1.Probability.FreshTupleRecurrence
public import PaperP1.Model.SourceConditionalDeviations
public import PaperP1.Model.FactorialBranching

/-! # Actual conditional fresh means give lower factorial-moment recurrences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FreshFactorialLower

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.SourceConditionalDeviations PaperP1.Probability

theorem joint_fresh_sum_eq (N L : ℕ) (A : Finset ℕ) (hq : 0 < infiniteJointMoment L A) :
    (∑ z ∈ dyadicBlock N \ A, infiniteJointMoment L (insert z A)) =
      infiniteJointMoment L A * freshMean N L A := by
  unfold freshMean conditionalStart
  rw [← sum_div]
  field_simp [hq.ne']

theorem factorial_succ_lower (N L r : ℕ) (m : ℝ)
    (hmean : ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      0 < infiniteJointMoment L A → m ≤ freshMean N L A) :
    m * factorialCountMoment (dyadicBlock N) L r ≤
      factorialCountMoment (dyadicBlock N) L (r + 1) := by
  rw [← sum_tuple_joint_moments (subset_refl _) r, ← sum_tuple_joint_moments (subset_refl _) (r + 1)]
  apply FreshTupleRecurrence.sum_succ_lower
  intro A hA hcard
  by_cases hq : 0 < infiniteJointMoment L A
  · rw [joint_fresh_sum_eq N L A hq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hmean A hA hcard hq) hq.le
  · have hz : infiniteJointMoment L A = 0 := le_antisymm (le_of_not_gt hq) (infiniteJointMoment_nonneg L A)
    rw [hz, mul_zero]
    exact sum_nonneg fun z _ ↦ infiniteJointMoment_nonneg L (insert z A)

theorem factorial_lower_power (N L k : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmean : ∀ r < k, ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      0 < infiniteJointMoment L A → m ≤ freshMean N L A) :
    m ^ k ≤ factorialCountMoment (dyadicBlock N) L k := by
  have hbound : ∀ r : ℕ, r ≤ k → m ^ r ≤ factorialCountMoment (dyadicBlock N) L r := by
    intro r
    induction r with
    | zero => intro _; rw [pow_zero, FactorialBranching.factorial_zero]
    | succ r ih =>
      intro hr
      calc
        _ = m * m ^ r := by rw [pow_succ]; ring
        _ ≤ m * factorialCountMoment (dyadicBlock N) L r :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hm
        _ ≤ _ := factorial_succ_lower N L r m (hmean r (by omega))
  exact hbound k le_rfl

end PaperP1.FreshFactorialLower
