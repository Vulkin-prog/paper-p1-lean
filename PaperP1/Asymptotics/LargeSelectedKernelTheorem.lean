module

public import PaperP1.Asymptotics.SelectedKernelCounts
public import PaperP1.Arithmetic.SelectedKernelSourceFamilies

/-! # Companion T1.6 for the actual separated mixed-square pair family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeSelectedKernelTheorem

open PaperP1.SelectedKernelSourceFamilies

theorem uniform_source_counts (C τ ε : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : ℝ, 0 < T →
        ((separatedPairs N L T).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) * T ^ (-1 / 2 + τ) ∧
        ((smallWindows N L T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * T ^ (1 / 2 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.SelectedKernelCounts.critical_counts C τ ε hτ hτhalf hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN L hcrit T hT
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hpairs, hwindows⟩ := hN₀ N (by omega) L hcrit T hT
  constructor
  · have hcard : (separatedPairs N L T).card ≤ (PaperP1.LargeAnchorPairs.bothPairs N (L + 1) T).card :=
      Finset.card_le_card (source_pairs_subset T hN2)
    exact (by exact_mod_cast hcard : ((separatedPairs N L T).card : ℝ) ≤
      (PaperP1.LargeAnchorPairs.bothPairs N (L + 1) T).card).trans hpairs
  · rw [small_windows_eq T hN2]
    exact hwindows

/-- One common threshold precedes every critical length and every source cutoff. -/
theorem companion_T1_6 (C τ ε : ℝ) (hτ : 0 < τ) (hτhalf : τ < 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : ℝ, 1 ≤ T → T ≤ 3 * N →
        ((separatedPairs N L T).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) * T ^ (-1 / 2 + τ) ∧
        ((smallWindows N L T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * T ^ (1 / 2 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := uniform_source_counts C τ ε hτ hτhalf.le hε
  exact ⟨N₀, fun N hN L hcrit T hT _hTupper ↦ hN₀ N hN L hcrit T (by linarith)⟩

end PaperP1.LargeSelectedKernelTheorem
