module

public import PaperP1.Model.ConnectedTriplePositiveReduction
public import PaperP1.Asymptotics.SharpPairTargetDeficit
public import PaperP1.Asymptotics.OriginalWindowFamilyMass

/-! # The positive connected triple seed reduces to A₃ with coefficient one and a sharp error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedTriplePositive

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_reduction (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        TripleJointPopulations.connectedJointMass G L ≤
          CompatibleActivitySplit.absolute L (connectedFamilies G L 3) + (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NP, _hNP, hpair⟩ := SharpPairTargetDeficit.article_11_1 C (ε / 2) (by positivity)
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 3 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NP + NI + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hd := (hpair N (by omega) L hband G hG).1
  have hind : FamilyIndependentMass.independentMass (connectedFamilies G L 3) L ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    simpa only [Nat.cast_ofNat] using (hi N (by omega) L G hband hG).2.2.1
  have hfactor : 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hfinite := ConnectedTriplePositiveReduction.finite_bound G L hL
  linarith only [hfinite, hd, hind, hfactor]

theorem uniform_absolute_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        |TripleJointPopulations.connectedJointMass G L -
          CompatibleActivitySplit.absolute L (connectedFamilies G L 3)| ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NP, _hNP, hpair⟩ := SharpPairTargetDeficit.article_11_1 C (ε / 2) (by positivity)
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 3 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 6 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NP + NI + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hd := (hpair N (by omega) L hband G hG).1
  have hind : FamilyIndependentMass.independentMass (connectedFamilies G L 3) L ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    simpa only [Nat.cast_ofNat] using (hi N (by omega) L G hband hG).2.2.1
  have hfactor : 6 * (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hfinite := ConnectedTriplePositiveReduction.absolute_error G L hL
  linarith only [hfinite, hd, hind, hfactor]

end PaperP1.ConnectedTriplePositive
