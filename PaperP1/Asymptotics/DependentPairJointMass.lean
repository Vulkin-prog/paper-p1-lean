module

public import PaperP1.Model.DependentPairJointActivity
public import PaperP1.Asymptotics.PairActivity

/-! # The complete actual dependent-pair joint mass has the sharp pair-activity rate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairJointMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, infiniteJointMoment L e) ≤
          (N : ℝ) ^ (-2 / 3 + ε) := by
  obtain ⟨NP, _hNP, hh⟩ := PairActivity.uniform_pair_activity C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨4 + NP + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  calc
    _ ≤ 2 * CompatibleActivitySplit.absolute L (G.powersetCard 2) := DependentPairJointActivity.finite_bound G L hL
    _ ≤ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) := mul_le_mul_of_nonneg_left (hh N (by omega) L hband G hG) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DependentPairJointMass
