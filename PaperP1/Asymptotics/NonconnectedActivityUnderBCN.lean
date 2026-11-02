module

public import PaperP1.Model.NonconnectedActivity
public import PaperP1.Asymptotics.CoarseFixedAbsoluteActivityUnderBCN

/-! # Nonconnected activity costs N^(-1+epsilon) at every fixed positive order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonconnectedActivityUnderBCN

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NonconnectedActivity
  PaperP1.ConnectedWindowFamilies

theorem uniform_block_mass (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      blockMass G L r ≤ (r + 1 : ℕ) * (N : ℝ) ^ (-1 / 2 + ε) := by
  have heach (s : ℕ) (hs : s ∈ Icc 2 r) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (connectedFamilies G L s) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    obtain ⟨NS, _hNS, hS⟩ := CoarseFixedAbsoluteActivityUnderBCN.uniform_connected_activity s
      (by have h := (mem_Icc.mp hs).1; omega) c κ hc hBCN C ε hε
    exact eventually_atTop.mpr ⟨NS, fun N hN ↦ hS N hN⟩
  obtain ⟨NF, hf⟩ := eventually_atTop.mp ((Finset.eventually_all (Icc 2 r)).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hcard : ((Icc 2 r).card : ℝ) ≤ (r + 1 : ℕ) := by
    exact_mod_cast (show (Icc 2 r).card ≤ r + 1 by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ s ∈ Icc 2 r, CompatibleActivitySplit.absolute L (connectedFamilies G L s) :=
      GraphStarWeights.sum_biUnion_le_nonneg (Icc 2 r) (fun s ↦ connectedFamilies G L s)
        (fun I ↦ |infiniteCenteredCoefficient L I|) (fun _ ↦ abs_nonneg _)
    _ ≤ ∑ _s ∈ Icc 2 r, (N : ℝ) ^ (-1 / 2 + ε) :=
      sum_le_sum fun s hs ↦ hf N (by omega) s hs L hband G hG
    _ = ((Icc 2 r).card : ℝ) * (N : ℝ) ^ (-1 / 2 + ε) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem uniform_activity (r : ℕ) (hr : 1 ≤ r) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (families G L r) ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  let R : ℝ := (r + 1 : ℕ)
  let D : ℝ := R ^ 2 / 2 * Real.exp R
  have hR : 0 ≤ R := Nat.cast_nonneg _
  obtain ⟨NB, _hNB, hb⟩ := uniform_block_mass r c κ hc hBCN C δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption D (-1 + 2 * δ) (ε / 2) (by positivity)
  refine ⟨max 2 (max NB (max NG NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let T := (N : ℝ) ^ (-1 / 2 + δ)
  let W := blockMass G L r
  have hT : 0 ≤ T := Real.rpow_nonneg hn.le _
  have hT1 : T ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδsmall] : -1 / 2 + δ ≤ 0)
  have hW0 : 0 ≤ W := sum_nonneg fun I _ ↦ abs_nonneg (infiniteCenteredCoefficient L I)
  have hW : W ≤ R * T := hb N (by omega) L hband G hG
  have hWR : W ≤ R := hW.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hT1 hR)
  have hsq := pow_le_pow_left₀ hW0 hW 2
  have hTsq : T ^ 2 = (N : ℝ) ^ (-1 + 2 * δ) := by
    calc
      _ = ((N : ℝ) ^ (-1 / 2 + δ)) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ = (N : ℝ) ^ ((-1 / 2 + δ) * 2) := (Real.rpow_mul hn.le _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (W ^ 2 / 2) * Real.exp W := NonconnectedActivity.finite_bound G L r hL hr
    _ ≤ ((R * T) ^ 2 / 2) * Real.exp R :=
      mul_le_mul (div_le_div_of_nonneg_right hsq (by norm_num))
        (Real.exp_le_exp.mpr hWR) (Real.exp_pos W).le (by positivity)
    _ = D * (N : ℝ) ^ (-1 + 2 * δ) := by rw [mul_pow, hTsq]; dsimp [D]; ring
    _ ≤ (N : ℝ) ^ ((-1 + 2 * δ) + ε / 2) := hf N (by omega)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε])

theorem uniform_absolute_difference (r : ℕ) (hr : 1 ≤ r) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard r) -
        CompatibleActivitySplit.absolute L (connectedFamilies G L r) ∧
      CompatibleActivitySplit.absolute L (G.powersetCard r) -
        CompatibleActivitySplit.absolute L (connectedFamilies G L r) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_activity r hr c κ hc hBCN C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  rw [NonconnectedActivity.absolute_difference]
  exact ⟨sum_nonneg (fun I _ ↦ abs_nonneg (infiniteCenteredCoefficient L I)), h N hN L hband G hG⟩

end PaperP1.NonconnectedActivityUnderBCN
