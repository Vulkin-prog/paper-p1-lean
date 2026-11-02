module

public import PaperP1.Model.TripleJointPopulations
public import PaperP1.Asymptotics.AlignedTripleCount
public import PaperP1.Asymptotics.NonalignedJointProbabilityUnderBCN
public import PaperP1.Asymptotics.OriginalWindowFamilyCounts

/-! # A first vanishing actual connected-triple joint mass under explicit BCN

This coarse exponent is much weaker than the manuscript's sharp triple
activity exponent. No dense-triple arithmetic estimate is assumed here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedTripleJointMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.TripleJointPopulations PaperP1.NonalignedJointProbabilityUnderBCN

theorem uniform_nonaligned_mass (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      nonalignedJointMass G L ≤ (N : ℝ) ^ (-tripleGap + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NC, hcount⟩ := OriginalWindowFamilyCounts.uniform_hosts 3 (by decide) C η hη
  obtain ⟨NP, hNP, hprob⟩ := uniform_family_probability c κ hc hBCN C η hη
  refine ⟨max 2 (max NC NP), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : ((nonalignedFamilies G L).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + η) := by
    have h := (hcount N (by omega) L G hband hG).1
    norm_num only [Nat.cast_ofNat] at h
    exact (show ((nonalignedFamilies G L).card : ℝ) ≤ (connectedFamilies G L 3).card by
      exact_mod_cast nonaligned_count_le G L).trans h
  calc
    _ ≤ ∑ _I ∈ nonalignedFamilies G L, (N : ℝ) ^ (-2 + rankSlope + η) := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hIG, _hcard, x, hx, y, hy, hxy, hnon⟩ := nonaligned_data hI
      exact hprob N (by omega) L hband I (hIG.trans hG) x hx y hy hxy hnon
    _ = ((nonalignedFamilies G L).card : ℝ) * (N : ℝ) ^ (-2 + rankSlope + η) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (3 / 2 + η) * (N : ℝ) ^ (-2 + rankSlope + η) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [tripleGap, η]; ring

theorem uniform_connected_mass (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      connectedJointMass G L ≤ (N : ℝ) ^ (-tripleGap + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NN, hNN, hnon⟩ := uniform_nonaligned_mass c κ hc hBCN C η hη
  obtain ⟨NA, hNA, haligned⟩ := AlignedTripleCount.uniform_joint_mass c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 2 (-tripleGap + η) η hη
  refine ⟨max NN (max NA NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ha : AlignedTripleFamilies.jointMass G L ≤ (N : ℝ) ^ (-tripleGap + η) :=
    (haligned N (by omega) L hband G hG).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [tripleGap_lt_half]))
  have hn := hnon N (by omega) L hband G hG
  calc
    _ ≤ AlignedTripleFamilies.jointMass G L + nonalignedJointMass G L := split_bound G L
    _ ≤ 2 * (N : ℝ) ^ (-tripleGap + η) := by linarith only [ha, hn]
    _ ≤ (N : ℝ) ^ ((-tripleGap + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_vanishing_mass (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      connectedJointMass G L ≤ (N : ℝ) ^ (-tripleGap / 2) := by
  have hgap := tripleGap_pos
  simpa only [show -tripleGap + tripleGap / 2 = -tripleGap / 2 by ring] using
    uniform_connected_mass c κ hc hBCN C (tripleGap / 2) (by positivity)

end PaperP1.CoarseConnectedTripleJointMass
