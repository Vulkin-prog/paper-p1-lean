module

public import PaperP1.Asymptotics.NonconnectedActivity
public import PaperP1.Asymptotics.CoarseConnectedActivity

/-! # Full actual absolute centered activity at every prescribed order at least three has exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullFixedActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NC, _hNC, hc⟩ := CoarseConnectedActivity.uniform_range R C (ε / 2) (by positivity)
  obtain ⟨ND, _hND, hd⟩ := NonconnectedActivity.uniform_bound R C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
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

end PaperP1.FullFixedActivity
