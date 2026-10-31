module

public import PaperP1.Arithmetic.WeightedPrimeSum
public import PaperP1.Analysis.ClippedPowerSum

/-! # An elementary reciprocal-power prime tail for every finite prime set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimePowerTail

open Finset PaperP1.DefectCounting PaperP1.WeightedPrimeSum
open PaperP1.ClippedPowerSum

def naturalClip (s Y : ℝ) (n : ℕ) : ℝ := min (Y ^ (-s)) ((n : ℝ) ^ (-s))

def constant (s : ℝ) : ℝ := Real.log 4 * (1 + PaperP1.PowerSeriesTail.constant s)

theorem naturalClip_succ (s Y : ℝ) (n : ℕ) :
    naturalClip s Y (n + 1) = clipped s Y n := by
  simp only [naturalClip, clipped, Nat.cast_add, Nat.cast_one]

theorem constant_pos (s : ℝ) (hs : 1 < s) : 0 < constant s := by
  unfold constant
  exact mul_pos (Real.log_pos (by norm_num))
    (by have h := PaperP1.PowerSeriesTail.constant_pos s hs; linarith)

theorem finite_prime_tail_mul_log_le (P : Finset ℕ) (s Y : ℝ)
    (hs : 1 < s) (hY : 1 < Y) (hP : ∀ p ∈ P, Nat.Prime p ∧ Y < (p : ℝ)) :
    (∑ p ∈ P, (p : ℝ) ^ (-s)) * Real.log Y ≤ constant s * Y ^ (1 - s) := by
  have hYpos : 0 < Y := by linarith
  have hsub : P ⊆ smallPrimesUpTo (P.sup id) := by
    intro p hp
    exact mem_smallPrimesUpTo.mpr ⟨(hP p hp).1, le_sup (f := id) hp⟩
  have hterm (p : ℕ) (hp : p ∈ P) :
      (p : ℝ) ^ (-s) * Real.log Y ≤ Real.log p * naturalClip s Y p := by
    have hpY := (hP p hp).2
    have hpow : (p : ℝ) ^ (-s) ≤ Y ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hYpos hpY.le (by linarith)
    rw [naturalClip, min_eq_right hpow]
    have hlog := Real.log_le_log hYpos hpY.le
    have h := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg p) (-s))
    simpa only [mul_comm] using h
  have hclip : ∀ i : ℕ, 0 ≤ naturalClip s Y (i + 1) := by
    intro i
    rw [naturalClip_succ]
    exact clipped_nonneg s Y hYpos.le i
  have hanti : Antitone (fun i : ℕ ↦ naturalClip s Y (i + 1)) := by
    simpa only [naturalClip_succ] using clipped_antitone s Y (by linarith)
  calc
    _ = ∑ p ∈ P, (p : ℝ) ^ (-s) * Real.log Y := by rw [sum_mul]
    _ ≤ ∑ p ∈ P, Real.log p * naturalClip s Y p := sum_le_sum hterm
    _ ≤ ∑ p ∈ smallPrimesUpTo (P.sup id), Real.log p * naturalClip s Y p := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.one_lt.le))
        (le_min (Real.rpow_nonneg hYpos.le _) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    _ ≤ Real.log 4 * ∑ i ∈ range (P.sup id), naturalClip s Y (i + 1) :=
      sum_log_prime_mul_le _ _ hclip hanti
    _ = Real.log 4 * ∑ i ∈ range (P.sup id), clipped s Y i := by simp only [naturalClip_succ]
    _ ≤ Real.log 4 * ((1 + PaperP1.PowerSeriesTail.constant s) * Y ^ (1 - s)) :=
      mul_le_mul_of_nonneg_left (clipped_sum_le s Y hs hY.le _) (Real.log_nonneg (by norm_num))
    _ = _ := by unfold constant; ring

theorem finite_prime_tail_le (P : Finset ℕ) (s Y : ℝ)
    (hs : 1 < s) (hY : 1 < Y) (hP : ∀ p ∈ P, Nat.Prime p ∧ Y < (p : ℝ)) :
    (∑ p ∈ P, (p : ℝ) ^ (-s)) ≤ constant s * Y ^ (1 - s) / Real.log Y :=
  (le_div_iff₀ (Real.log_pos hY)).mpr (finite_prime_tail_mul_log_le P s Y hs hY hP)

end PaperP1.PrimePowerTail
