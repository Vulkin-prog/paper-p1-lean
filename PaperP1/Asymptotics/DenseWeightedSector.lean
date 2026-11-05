module

public import PaperP1.Asymptotics.DenseComponentPairHosts
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # The complete dense weighted pair sector is unconditional, including the full value kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseWeightedSector

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RawPairRelationRank
  PaperP1.LargePrimeGraphResolution

theorem uniform_full_weight (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
      (∑ p ∈ F, (2 ^ fullRank p.1 p.2 L : ℝ)) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := DenseComponentPairHosts.uniform_hosts C η (ε / 2) hη (by positivity)
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.uniform_global C (ε / 2) (by positivity)
  refine ⟨3 + NH + NP, by omega, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  have hcount := hh N (by omega) L hband F hdyadic hnon hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ _p ∈ F, (N : ℝ) ^ (1 + ε / 2) := sum_le_sum fun p hpF ↦
      hp N (by omega) L hband p.1 (hdyadic p hpF).1 p.2 (hdyadic p hpF).2
    _ = (F.card : ℝ) * (N : ℝ) ^ (1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_kernels (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
      (∑ p ∈ F, ((2 ^ fullRank p.1 p.2 L : ℝ) - 1)) ≤ (N : ℝ) ^ (1 + ε) ∧
      (∑ p ∈ F, ((2 ^ runRelativeNullity L {p.1, p.2} : ℝ) - 1)) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_full_weight C ε η hε hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  have hm := h N hN L hband F hdyadic hnon hdense
  constructor
  · apply le_trans (sum_le_sum fun p _ ↦ sub_le_self _ zero_le_one) hm
  · apply le_trans (sum_le_sum fun p _ ↦ ?_) hm
    exact (sub_le_self _ zero_le_one).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (relative_le_full p.1 p.2 L))

end PaperP1.DenseWeightedSector
