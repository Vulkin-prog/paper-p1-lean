module

public import PaperP1.Asymptotics.CoarseConnectedTripleJointMassUnderInputs
public import PaperP1.Asymptotics.ConnectedTriplePositiveUnderInputs

/-! # The full actual connected third centered activity has coarse rate1, including affine incompatibility -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedTripleActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters,
      ∃ pi pb pe : FinitePairDeficitInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pi (GeneralGraphHostCount.sizeCap (ε / 16384)) →
      FinitePairDeficitInputs.Hypotheses pb (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      FinitePairDeficitInputs.Hypotheses pe (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        CompatibleActivitySplit.absolute L (connectedFamilies G L 3) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨pd, pi, pb, hq⟩ := CoarseConnectedTripleJointMassUnderInputs.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨pe, he⟩ := ConnectedTriplePositiveUnderInputs.uniform_absolute_error C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨pd, pi, pb, pe, ?_⟩
  intro hgeoD hgeoI hgeoB hgeoE
  have hsI : (ε / 2) / 8192 = ε / 16384 := by ring
  have hsB : (ε / 2) / 1024 = ε / 2048 := by ring
  obtain ⟨NQ, _hNQ, hq⟩ := hq hgeoD (by simpa only [hsI] using hgeoI)
    (by simpa only [hsB] using hgeoB)
  obtain ⟨NE, _hNE, he⟩ := he (by simpa only [hsB] using hgeoE)
  refine ⟨10 + NQ + NE + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hmass : TripleJointPopulations.connectedJointMass G L ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    hq N (by omega) L hband G hG (connectedFamilies G L 3) Subset.rfl
  have herr := (abs_le.mp (he N (by omega) L hband G hG)).1
  have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hmass, herr, hpower, hfactor]

end PaperP1.CoarseConnectedTripleActivityUnderInputs
