module

public import PaperP1.Model.RetainedModifiedLaw

/-! # Every-order bounds for the actual retained-configuration modified count

Its coupling error is kept as the literal bad-event probability. No
asymptotic or smallness estimate for that probability is a hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedModifiedBounds

open MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.RetainedActiveCount PaperP1.RetainedCountCylinder
  PaperP1.DirectActiveEnvelope PaperP1.HeterogeneousDirectMaximum

local instance retainedModifiedBoundsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem expected_factorial (H : ℝ) (N L : ℕ) (G : Finset ℕ) (hL : 0 < L) (r : ℕ) :
    (∫ ω, ((modified H N L G ω).descFactorial (r + 1) : ℝ) ∂infiniteRademacherMeasure) ≤
      actualMean G L ^ (r + 1) + (r + 1 : ℕ) * actualMean G L ^ r := by
  calc
    _ ≤ ∫ ω, ((envelope G L ω).descFactorial (r + 1) : ℝ) ∂infiniteRademacherMeasure := by
      apply integral_mono
        (RetainedCountCylinder.observable_integrable H N L G (fun n ↦ (n.descFactorial (r + 1) : ℝ)))
        (DirectActiveEnvelope.observable_integrable G L (fun n ↦ (n.descFactorial (r + 1) : ℝ)))
      intro ω
      change ((modified H N L G ω).descFactorial (r + 1) : ℝ) ≤
        ((envelope G L ω).descFactorial (r + 1) : ℝ)
      exact_mod_cast Nat.descFactorial_le (r + 1) (modified_le_envelope H N L G ω)
    _ ≤ _ := envelope_factorial G L hL r

theorem expected_power (H : ℝ) (N L : ℕ) (G : Finset ℕ) (hL : 0 < L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤
      s * ∏ x ∈ G, (1 + (s - 1) * infiniteMarginal x L) ∧
    (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤ s * Real.exp ((s - 1) * actualMean G L) := by
  have hle : (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤
      ∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure := by
    apply integral_mono (RetainedCountCylinder.observable_integrable H N L G (fun n ↦ s ^ n))
      (DirectActiveEnvelope.observable_integrable G L (fun n ↦ s ^ n))
    intro ω
    exact pow_le_pow_right₀ hs (modified_le_envelope H N L G ω)
  have hb := envelope_power G L hL s hs
  exact ⟨hle.trans hb.1, hle.trans hb.2⟩

theorem tail_probability (H : ℝ) (N L : ℕ) (G : Finset ℕ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k) :
    infiniteRademacherMeasure.real {ω | k ≤ modified H N L G ω} ≤ actualMean G L ^ (k - 1) / (k - 1).factorial := by
  calc
    _ ≤ infiniteRademacherMeasure.real {ω | k ≤ envelope G L ω} :=
      measureReal_mono (fun ω hω ↦ le_trans hω (modified_le_envelope H N L G ω))
    _ ≤ _ := envelope_tail G L hL k hk

theorem original_tail (H : ℝ) (N L : ℕ) (G : Finset ℕ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k) :
    infiniteRademacherMeasure.real {ω | k ≤ infiniteStartCount G L ω} ≤
      actualMean G L ^ (k - 1) / (k - 1).factorial + badProbability H N L G := by
  have hsub : {ω | k ≤ infiniteStartCount G L ω} ⊆
      {ω | k ≤ modified H N L G ω} ∪ {ω | ¬ retainedActive H N L G ω} := by
    intro ω hω
    by_cases hr : retainedActive H N L G ω
    · left
      change k ≤ modified H N L G ω
      unfold modified
      rw [ite_eq_left hr]
      exact hω
    · exact Or.inr hr
  calc
    _ ≤ infiniteRademacherMeasure.real
        ({ω | k ≤ modified H N L G ω} ∪ {ω | ¬ retainedActive H N L G ω}) := measureReal_mono hsub
    _ ≤ infiniteRademacherMeasure.real {ω | k ≤ modified H N L G ω} + badProbability H N L G :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add (tail_probability H N L G hL k hk) le_rfl

theorem regular_mean {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) : actualMean G L = MaximumDirectActive.mean G L :=
  (actualMean_eq_countMoment (hG.trans (RegularStarts.regularStarts_subset N L))).trans
    (MaximumDirectActive.mean_eq_actual hN hL G hG).symm

theorem expected_power_regular (H : ℝ) {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤
      s * (1 + (2 ^ L : ℝ)⁻¹ * (s - 1)) ^ G.card := by
  calc
    _ ≤ s * ∏ x ∈ G, (1 + (s - 1) * infiniteMarginal x L) := (expected_power H N L G hL s hs).1
    _ = _ := by
      congr 1
      calc
        _ = ∏ _x ∈ G, (1 + (2 ^ L : ℝ)⁻¹ * (s - 1)) := by
          apply Finset.prod_congr rfl
          intro x hx
          have hxpos : 0 < x := by
            have h := (Finset.mem_Ico.mp ((RegularStarts.regularStarts_subset N L) (hG hx))).1
            omega
          rw [RegularStarts.marginal_on_regular hxpos hL (hG hx)]
          ring
        _ = _ := by simp

theorem companion_T19_3_bounds (H : ℝ) {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (G : Finset ℕ) (hG : G ⊆ RegularStarts.regularStarts N L)
    (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (s : ℝ) (hs : 1 ≤ s) :
    infiniteRademacherMeasure.real {ω | k ≤ infiniteStartCount G L ω} ≤
      MaximumDirectActive.mean G L ^ (k - 1) / (k - 1).factorial + badProbability H N L G ∧
    infiniteRademacherMeasure.real {ω | k ≤ modified H N L G ω} ≤
      MaximumDirectActive.mean G L ^ (k - 1) / (k - 1).factorial ∧
    (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤
      s * (1 + (2 ^ L : ℝ)⁻¹ * (s - 1)) ^ G.card ∧
    (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤
      s * Real.exp ((s - 1) * MaximumDirectActive.mean G L) ∧
    (∫ ω, ((modified H N L G ω).descFactorial r : ℝ) ∂infiniteRademacherMeasure) ≤
      MaximumDirectActive.mean G L ^ r + (r : ℝ) * MaximumDirectActive.mean G L ^ (r - 1) := by
  have hm := regular_mean hN hL G hG
  refine ⟨?_, ?_, expected_power_regular H hN hL G hG s hs, ?_, ?_⟩
  · simpa only [hm] using original_tail H N L G hL k hk
  · simpa only [hm] using tail_probability H N L G hL k hk
  · simpa only [hm] using (expected_power H N L G hL s hs).2
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    simpa only [hm, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using expected_factorial H N L G hL j

end PaperP1.RetainedModifiedBounds
