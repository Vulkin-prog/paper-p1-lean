module

public import PaperP1.Model.SignedPrivateField
public import PaperP1.Model.CleanPivotWordCost
public import PaperP1.Probability.WeightedPositiveForcingCostLower

/-! # Exact clean-pair contributions to the original signed forcing cost

The forcing is the specified prime-cylinder map of SignedPrivateField.
Each selected pair keeps its own actual source and target mark lengths.
No uniform marginal, target flip or Palm cost is substituted as a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedPrivateCleanCost

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.SignedExactWords PaperP1.SignedPrivateField PaperP1.CleanPivotTargets
  PaperP1.PrivatePivotTargetFlip PaperP1.Probability PaperP1.Algebra
  PaperP1.PositiveForcingCostLower PaperP1.UniformFubini

variable {M Y L E : ℕ} {J : Finset ℕ}

theorem indicator_eq_word (D : Data M Y L E J) (a : Index J E) (ω : SampleSpace M) :
    (indicatorValue (indicator M L a ω) : ℝ) =
      if valueSystem M (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val) ω =
          signedExactWord L a.2.1.val a.2.2 then 1 else 0 := by
  classical
  have hi := finite_signedWord_iff (j := a.1.val) (e := a.2.1.val) D.length_pos a.2.2 ω
  by_cases hw : valueSystem M (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val) ω =
      signedExactWord L a.2.1.val a.2.2
  · have hb : indicator M L a ω = true := decide_eq_true (hi.mp hw)
    rw [hb, ite_eq_left hw]
    rfl
  · have hn := fun h ↦ hw (hi.mpr h)
    have hb : indicator M L a ω = false := decide_eq_false hn
    rw [hb, ite_eq_right hw]
    rfl

theorem target_width_le_pivot (D : Data M Y L E J) (a b : Index J E)
    (selected : Fin (L + a.2.1.val + 2)) :
    L + b.2.1.val + 2 ≤ (pivots D a selected).val.val := by
  change L + b.2.1.val + 2 ≤ PaperP1.OddPrimePivot.largestOddPrime (a.1.val + selected.val)
  have hb := b.2.1.isLt
  exact (by have := D.small_cutoff; omega : L + b.2.1.val + 2 ≤ Y).trans
    (actual_good D a selected).le

theorem expected_change_clean (D : Data M Y L E J) (a b : Index J E)
    (selected : Fin (L + a.2.1.val + 2)) {A N : ℕ}
    (hclean : b.1.val ∈ targets A N (pivots D a selected).val.val
      (L + b.2.1.val + 2) (otherPrimes (pivots D a) selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val)
      (fun i : Fin (L + b.2.1.val + 2) ↦ b.1.val + i.val))) :
    finiteExpectation (cylinderProbability M).weight (fun ω ↦
      |(indicatorValue (indicator M L b ω) : ℝ) - indicatorValue (indicator M L b (force D a ω))|) =
      signedMarkRate L b.2.1.val := by
  have hc := PaperP1.CleanPivotWordCost.signed_actual_cost
    (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val) (pivots D a)
    (signedExactWord L a.2.1.val a.2.2) selected (signedExactWord L b.2.1.val b.2.2)
    (target_width_le_pivot D a b selected) hclean hjoint
  simp_rw [indicator_eq_word D]
  exact hc

theorem clean_weight (D : Data M Y L E J) (a b : Index J E)
    (selected : Fin (L + a.2.1.val + 2)) {A N : ℕ}
    (hclean : b.1.val ∈ targets A N (pivots D a selected).val.val
      (L + b.2.1.val + 2) (otherPrimes (pivots D a) selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val)
      (fun i : Fin (L + b.2.1.val + 2) ↦ b.1.val + i.val))) :
    weight (cylinderProbability M) (indicator M L) (force D) (a, b) =
      signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val := by
  unfold weight
  rw [indicator_marginal D, expected_change_clean D a b selected hclean hjoint]

theorem selected_pairs_lower (D : Data M Y L E J)
    (P : Finset (Index J E × Index J E))
    (hP : P ⊆ directed univ) {A N : ℕ}
    (hclean : ∀ p ∈ P, ∃ selected : Fin (L + p.1.2.1.val + 2),
      p.2.1.val ∈ targets A N (pivots D p.1 selected).val.val
        (L + p.2.2.1.val + 2) (otherPrimes (pivots D p.1) selected))
    (hjoint : ∀ p ∈ P, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (L + p.1.2.1.val + 2) ↦ p.1.1.val + i.val)
      (fun i : Fin (L + p.2.2.1.val + 2) ↦ p.2.1.val + i.val))) :
    (∑ p ∈ P, signedMarkRate L p.1.2.1.val * signedMarkRate L p.2.2.1.val) ≤ cost D := by
  have h := PaperP1.WeightedPositiveForcingCostLower.full_selected_sum univ
    (cylinderProbability M) (indicator M L) (force D) (fun a _ ω ↦ force_hits D a ω) P hP
  change _ ≤ cost D at h
  refine (sum_congr rfl (fun p hp ↦ ?_)).le.trans h
  obtain ⟨i, hi⟩ := hclean p hp
  exact (clean_weight D p.1 p.2 i hi (hjoint p hp)).symm

theorem selected_zero_pairs_lower (D : Data M Y L E J)
    (P : Finset (Index J E × Index J E))
    (hP : P ⊆ directed univ) {A N : ℕ}
    (hclean : ∀ p ∈ P, ∃ selected : Fin (L + p.1.2.1.val + 2),
      p.2.1.val ∈ targets A N (pivots D p.1 selected).val.val
        (L + p.2.2.1.val + 2) (otherPrimes (pivots D p.1) selected))
    (hjoint : ∀ p ∈ P, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (L + p.1.2.1.val + 2) ↦ p.1.1.val + i.val)
      (fun i : Fin (L + p.2.2.1.val + 2) ↦ p.2.1.val + i.val)))
    (hzero : ∀ p ∈ P, p.1.2.1.val = 0 ∧ p.2.2.1.val = 0) :
    (signedMarkRate L 0) ^ 2 * P.card ≤ cost D := by
  calc
    _ = ∑ _p ∈ P, (signedMarkRate L 0) ^ 2 := by simp [mul_comm]
    _ = ∑ p ∈ P, signedMarkRate L p.1.2.1.val * signedMarkRate L p.2.2.1.val := by
      apply sum_congr rfl
      intro p hp
      rw [(hzero p hp).1, (hzero p hp).2, pow_two]
    _ ≤ cost D := selected_pairs_lower D P hP hclean hjoint

end PaperP1.SignedPrivateCleanCost
