module

public import PaperP1.Asymptotics.NonconnectedActivityUnderInputs
public import PaperP1.Asymptotics.CoarseConnectedActivityUnderInputs

/-! # Full actual absolute centered activity at every prescribed order at least three has exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullFixedActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pc pi pd : Parameters R, ∃ pp pq : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 32) → Hypotheses pi (ε / 128) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 131072)) →
      Hypotheses pd (min (ε / 8) (1 / 12) / 8) →
      FinitePairDeficitInputs.Hypotheses pq (GeneralGraphHostCount.sizeCap (min (ε / 8) (1 / 12) / 8192)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨pc, pi, pp, hc⟩ := CoarseConnectedActivityUnderInputs.uniform_range R C (ε / 2) (by positivity)
  obtain ⟨pd, pq, hd⟩ := NonconnectedActivityUnderInputs.uniform_bound R C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨pc, pi, pd, pp, pq, ?_⟩
  intro hgeoC hgeoI hgeoP hgeoD hgeoQ
  have hsC : (ε / 2) / 16 = ε / 32 := by ring
  have hsI : (ε / 2) / 64 = ε / 128 := by ring
  have hsP : (ε / 2) / 65536 = ε / 131072 := by ring
  have hsD : (ε / 2) / 4 = ε / 8 := by ring
  obtain ⟨NC, _hNC, hc⟩ := hc (by simpa only [hsC] using hgeoC)
    (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP)
  obtain ⟨ND, _hND, hd⟩ := hd (by simpa only [hsD] using hgeoD) (by simpa only [hsD] using hgeoQ)
  refine ⟨10 + NC + ND + NF, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG
  let P := Connected L
  let FC := (G.powersetCard r).filter P
  let FD := (G.powersetCard r).filter fun I ↦ ¬ P I
  have hC : (∑ I ∈ FC, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    hc N (by omega) L hband r hthree hcap G hG FC Subset.rfl
  have hD : (∑ I ∈ FD, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply (hd N (by omega) L hband G hG FD ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
    · intro I hI
      obtain ⟨hIG, hnot⟩ := mem_filter.mp hI
      obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp hIG
      exact ⟨hIG, card_pos.mp (by omega), by omega, hnot⟩
  have hsplit := sum_filter_add_sum_filter_not (G.powersetCard r) P (fun I ↦ |infiniteCenteredCoefficient L I|)
  change (∑ I ∈ FC, |infiniteCenteredCoefficient L I|) +
    (∑ I ∈ FD, |infiniteCenteredCoefficient L I|) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hC, hD, hsplit, hfactor]

end PaperP1.FullFixedActivityUnderInputs
