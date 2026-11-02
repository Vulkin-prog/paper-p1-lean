module

public import PaperP1.Model.JointBranchingEvents
public import PaperP1.Arithmetic.FiniteChannelHierarchy

/-! # Actual conditional start masses and their positive/negative deviations

Conditioning is on all prescribed start events in the actual source set.
The denominator is its actual positive joint probability, with no common
or nominal replacement of source marginals.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceConditionalDeviations

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.JointBranchingEvents
  PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget PaperP1.FiniteChannelHierarchy

def conditionalStart (A : Finset ℕ) (L z : ℕ) : ℝ :=
  infiniteJointMoment L (insert z A) / infiniteJointMoment L A

def freshMean (N L : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ z ∈ dyadicBlock N \ A, conditionalStart A L z

def positiveDeviation (N L : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ z ∈ dyadicBlock N \ A, max 0 (conditionalStart A L z - (2 ^ L : ℝ)⁻¹)

def negativeDeviation (N L : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ z ∈ dyadicBlock N \ A, max 0 ((2 ^ L : ℝ)⁻¹ - conditionalStart A L z)

theorem conditional_nonneg (A : Finset ℕ) (L z : ℕ) : 0 ≤ conditionalStart A L z :=
  div_nonneg (infiniteJointMoment_nonneg L _) (infiniteJointMoment_nonneg L A)

theorem conditional_le_one (A : Finset ℕ) (L z : ℕ) (hq : 0 < infiniteJointMoment L A) :
    conditionalStart A L z ≤ 1 := by
  unfold conditionalStart
  exact (div_le_one hq).mpr (infiniteJointMoment_antitone L (subset_insert z A))

theorem conditional_probability_ratio (A : Finset ℕ) (L z : ℕ) (hL : 0 < L) :
    conditionalStart A L z =
      Model.InfiniteRademacher.infiniteRademacherMeasure.real (jointEvent (insert z A) L) /
        Model.InfiniteRademacher.infiniteRademacherMeasure.real (jointEvent A L) := by
  simp only [conditionalStart, infiniteJointMoment_eq_probability _ hL]

theorem retained_conditional {N L z : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hA : A ⊆ dyadicBlock N)
    (hz : z ∈ dyadicBlock N) (hnot : z ∉ badStarts N L (rawValues A L))
    (hq : 0 < infiniteJointMoment L A) : conditionalStart A L z = (2 ^ L : ℝ)⁻¹ := by
  unfold conditionalStart
  rw [retained_joint_factor hN hL hA hz hnot, mul_div_cancel_right₀ _ hq.ne']

theorem positive_nonneg (N L : ℕ) (A : Finset ℕ) : 0 ≤ positiveDeviation N L A :=
  sum_nonneg fun _ _ ↦ le_max_left _ _

theorem negative_nonneg (N L : ℕ) (A : Finset ℕ) : 0 ≤ negativeDeviation N L A :=
  sum_nonneg fun _ _ ↦ le_max_left _ _

theorem finite_negative_bound {N L : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hA : A ⊆ dyadicBlock N)
    (hq : 0 < infiniteJointMoment L A) :
    negativeDeviation N L A ≤ (badStarts N L (rawValues A L)).card * (2 ^ L : ℝ)⁻¹ := by
  classical
  let E := badStarts N L (rawValues A L)
  have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ := by positivity
  have hpoint (z : ℕ) (hz : z ∈ dyadicBlock N \ A) :
      max 0 ((2 ^ L : ℝ)⁻¹ - conditionalStart A L z) ≤
        if z ∈ E then (2 ^ L : ℝ)⁻¹ else 0 := by
    by_cases hE : z ∈ E
    · rw [ite_eq_left hE]
      exact max_le hp (by linarith only [conditional_nonneg A L z])
    · rw [ite_eq_right hE, retained_conditional hN hL hA (mem_sdiff.mp hz).1 hE hq,
        sub_self, max_self]
  calc
    _ ≤ ∑ z ∈ dyadicBlock N \ A, if z ∈ E then (2 ^ L : ℝ)⁻¹ else 0 := sum_le_sum hpoint
    _ ≤ ∑ z ∈ dyadicBlock N, if z ∈ E then (2 ^ L : ℝ)⁻¹ else 0 :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ ↦ by split_ifs <;> positivity)
    _ = E.card * (2 ^ L : ℝ)⁻¹ := by
      rw [← sum_filter]
      have hfilter : (dyadicBlock N).filter (fun z ↦ z ∈ E) = E := by
        ext z
        simp only [mem_filter]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨badStarts_subset N L (rawValues A L) h, h⟩⟩
      rw [hfilter, sum_const, nsmul_eq_mul]

theorem mean_decomposition {N L : ℕ} {A : Finset ℕ} (hA : A ⊆ dyadicBlock N) :
    freshMean N L A = nominalMean N L - A.card * (2 ^ L : ℝ)⁻¹ +
      positiveDeviation N L A - negativeDeviation N L A := by
  have hcard : (((dyadicBlock N \ A).card : ℝ) + A.card) = N := by
    exact_mod_cast (card_sdiff_add_card_eq_card hA).trans (dyadicBlock_card N)
  have hpoint (z : ℕ) : conditionalStart A L z = (2 ^ L : ℝ)⁻¹ +
      max 0 (conditionalStart A L z - (2 ^ L : ℝ)⁻¹) -
      max 0 ((2 ^ L : ℝ)⁻¹ - conditionalStart A L z) := by
    rcases le_total (conditionalStart A L z) ((2 ^ L : ℝ)⁻¹) with h | h
    · rw [max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]
      ring
  unfold freshMean
  calc
    _ = ∑ z ∈ dyadicBlock N \ A, ((2 ^ L : ℝ)⁻¹ +
        max 0 (conditionalStart A L z - (2 ^ L : ℝ)⁻¹) -
        max 0 ((2 ^ L : ℝ)⁻¹ - conditionalStart A L z)) :=
      sum_congr rfl (fun z _ ↦ hpoint z)
    _ = ((dyadicBlock N \ A).card : ℝ) * (2 ^ L : ℝ)⁻¹ +
        positiveDeviation N L A - negativeDeviation N L A := by
      rw [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
      rfl
    _ = _ := by unfold nominalMean; rw [← hcard]; ring

theorem finite_mean_lower {N L : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hA : A ⊆ dyadicBlock N)
    (hq : 0 < infiniteJointMoment L A) :
    nominalMean N L - (A.card + (badStarts N L (rawValues A L)).card) * (2 ^ L : ℝ)⁻¹ ≤
      freshMean N L A := by
  rw [mean_decomposition hA]
  have hp := positive_nonneg N L A
  have hn := finite_negative_bound hN hL hA hq
  linarith only [hp, hn]

end PaperP1.SourceConditionalDeviations
