module

public import PaperP1.Asymptotics.CriticalFreshBranchingBudget
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Model.SequentialRetainedWindows

/-! # Every actual ordered retained extension of a pair has the critical uniform mass budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalSequentialPairMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CriticalFreshBranchingBudget PaperP1.SequentialBranchingPaths

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_pair (K C : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ, 2 ≤ m →
      (m : ℝ) ≤ orderCap K N → ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e ⊆ dyadicBlock N → e.card = 2 →
      ∀ k : ℕ, k + 2 ≤ m →
        |SequentialRetainedWindows.mass N L e k -
          ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e| ≤
        (((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e) *
          ((k : ℝ) * freshEnvelope K N / N) := by
  obtain ⟨NB, _hNB, hb⟩ := CriticalOrderBranching.uniform_exception_bound K C hK
  obtain ⟨ND, _hND, hd⟩ := uniform_small_budget K (1 / 12) hK (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max 3 (max NB (max ND NG)), by omega, ?_⟩
  intro N hN m hm horder L hband e heG hecard k hkm
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  let D := freshEnvelope K N
  have hD : 0 ≤ D := (freshEnvelope_pos K N).le
  have hDN : D ≤ (dyadicBlock N).card := by
    rw [dyadicBlock_card]
    exact (hd N (by omega)).1
  have hcount : ∀ S ⊆ dyadicBlock N, S.card ≤ e.card + (m - 2) →
      ((dyadicBlock N).card : ℝ) - D ≤ (SequentialRetainedWindows.next N L S).card := by
    intro S hS hcard
    have hSm : S.card ≤ m := by rw [hecard] at hcard; omega
    have hbad := hb N (by omega) m horder L hband S hS hSm
    have hmR : (m : ℝ) ≤ max 0 (orderCap K N) := horder.trans (le_max_right _ _)
    have hDcompare : CriticalBranchingBudget.exceptionEnvelope K N + m ≤ D := by
      dsimp [D, freshEnvelope]
      linarith only [hmR]
    rw [dyadicBlock_card]
    exact (sub_le_sub_left hDcompare (N : ℝ)).trans
      (SequentialRetainedWindows.next_card_lower S hS hSm _ hbad)
  have hstep : ∀ S ⊆ dyadicBlock N, ∀ z ∈ SequentialRetainedWindows.next N L S,
      infiniteJointMoment L (insert z S) = (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L S := by
    intro S hS z hz
    have hh := (SequentialRetainedWindows.mem_next N L z S).mp hz
    exact JointBranchingEvents.retained_joint_factor (by omega) hL hS hh.1 hh.2.2
  have hmass := SequentialBranchingPaths.mass_error (dyadicBlock N) (SequentialRetainedWindows.next N L) e
    (m - 2) heG (fun S _ ↦ SequentialRetainedWindows.next_subset N L S) D hD hDN hcount
    (infiniteJointMoment L) ((2 ^ L : ℝ)⁻¹) (by positivity) (infiniteJointMoment_nonneg L e) hstep k (by omega)
  rw [dyadicBlock_card] at hmass
  change |SequentialRetainedWindows.mass N L e k -
    ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e| ≤ _ at hmass
  by_cases hk : k = 0
  · subst k
    simpa only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, one_mul] using hmass
  · have hpow : (N : ℝ) ^ k = (N : ℝ) ^ (k - 1) * N := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have heq : (((2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e) *
        (D * k * (N : ℝ) ^ (k - 1)) =
        (((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e) * ((k : ℝ) * D / N) := by
      rw [mul_pow, hpow]
      field_simp
    exact hmass.trans_eq heq

theorem relative_of_bound {N L k : ℕ} {e : Finset ℕ} (hN : 0 < N)
    (hq : 0 < infiniteJointMoment L e) (D : ℝ)
    (h : |SequentialRetainedWindows.mass N L e k -
      ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e| ≤
      (((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e) * ((k : ℝ) * D / N)) :
    |SequentialRetainedWindows.mass N L e k /
      (((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e) - 1| ≤ (k : ℝ) * D / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let B := ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L e
  have hB : 0 < B := by dsimp [B]; positivity
  have heq : SequentialRetainedWindows.mass N L e k / B - 1 =
      (SequentialRetainedWindows.mass N L e k - B) / B := by field_simp
  change |SequentialRetainedWindows.mass N L e k / B - 1| ≤ _
  rw [heq, abs_div, abs_of_pos hB]
  exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using h)

end PaperP1.CriticalSequentialPairMass
