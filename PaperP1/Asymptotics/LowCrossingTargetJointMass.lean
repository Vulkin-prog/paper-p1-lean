module

public import PaperP1.Asymptotics.IndependentTargetMass
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Model.OneTargetCrossing

/-! # True fixed-source conditional cost below a reciprocal crossing threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowCrossingTargetJointMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (s b : ℕ) (hb : 0 < b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N →
      ∀ S : Finset ℕ, S ⊆ dyadicBlock N →
      (∀ z ∈ S, z ∉ e ∧ 0 < OneTargetCrossing.rank e L z ∧
        (OneTargetCrossing.rank e L z : ℝ) < (L : ℝ) / b) →
        (∑ z ∈ S, infiniteJointMoment L (insert z e)) ≤
          infiniteJointMoment L e * (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / (b : ℝ) + ε) := by
  obtain ⟨NI, hi⟩ := IndependentTargetMass.uniform_mass s C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let K := (2 : ℝ) ^ ((C + 1) / b)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K
    (-(1 : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NI + NG + NA, by omega, ?_⟩
  intro N hN L hband e he heG S hSG hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsub : S ⊆ WindowTargetHosts.targets (dyadicBlock N) L e := by
    intro z hz
    exact OneTargetCrossing.mem_targets _ e L z (hSG hz) (hS z hz).1 (hS z hz).2.1
  have hmass : (∑ z ∈ S, infiniteMarginal z L) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg z L)).trans
      (hi N (by omega) L (dyadicBlock N) e hband Subset.rfl heG he)
  have hpow (z : ℕ) (hz : z ∈ S) : (2 ^ OneTargetCrossing.rank e L z : ℝ) ≤
      K * (N : ℝ) ^ (1 / (b : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (OneTargetCrossing.rank e L z : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ((hS z hz).2.2.le.trans
          (div_le_div_of_nonneg_right (by push_cast; linarith) hbR.le))
      _ ≤ _ := CriticalChannelPowers.window_root_upper (by omega) hb hband
  calc
    _ ≤ ∑ z ∈ S, (infiniteJointMoment L e * (K * (N : ℝ) ^ (1 / (b : ℝ)))) * infiniteMarginal z L := by
      apply sum_le_sum
      intro z hz
      exact (OneTargetCrossing.joint_upper e L z hL (hS z hz).1).trans
        ((mul_le_mul_of_nonneg_left (hpow z hz) (mul_nonneg (infiniteJointMoment_nonneg L e)
          (MissingBlockProbabilities.infiniteMarginal_nonneg z L))).trans_eq (by ring))
    _ = (infiniteJointMoment L e * (K * (N : ℝ) ^ (1 / (b : ℝ)))) * ∑ z ∈ S, infiniteMarginal z L := by
      rw [mul_sum]
    _ ≤ (infiniteJointMoment L e * (K * (N : ℝ) ^ (1 / (b : ℝ)))) * (N : ℝ) ^ (-(1 : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (infiniteJointMoment_nonneg L e)
        (mul_nonneg hK (Real.rpow_nonneg hn.le _)))
    _ = infiniteJointMoment L e * (K * (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / (b : ℝ) + ε / 2)) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ infiniteJointMoment L e * (N : ℝ) ^ ((-(1 : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) + ε / 2) :=
      mul_le_mul_of_nonneg_left (ha N (by omega)) (infiniteJointMoment_nonneg L e)
    _ = _ := by congr 2; ring

end PaperP1.LowCrossingTargetJointMass
