module

public import PaperP1.Model.DependentPairJointActivity
public import PaperP1.Asymptotics.SharpPairTargetDeficitUnderInputs
public import PaperP1.Asymptotics.FinitePairDeficitInputs

/-! # The complete actual dependent-pair joint mass has the sharp pair-activity rate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairJointMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FinitePairDeficitInputs

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 1024)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, infiniteJointMoment L e) ≤
          (N : ℝ) ^ (-2 / 3 + ε) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hp⟩ := SharpPairTargetDeficitUnderInputs.article_11_1 C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨⟨Ds, k, k₁, k₂, hDs⟩, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 512 = ε / 1024 := by ring
  obtain ⟨NP, _hNP, hh⟩ := hp (by simpa only [hscale] using hgeo.source)
    hgeo.ordinaryTwo hgeo.ordinaryThree hgeo.sourceCurves hgeo.ordinaryTwoCurves hgeo.ordinaryThreeCurves
  refine ⟨4 + NP + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  calc
    _ ≤ 2 * CompatibleActivitySplit.absolute L (G.powersetCard 2) := DependentPairJointActivity.finite_bound G L hL
    _ ≤ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) := mul_le_mul_of_nonneg_left (hh N (by omega) L hband G hG).2 (by norm_num)
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DependentPairJointMassUnderInputs
