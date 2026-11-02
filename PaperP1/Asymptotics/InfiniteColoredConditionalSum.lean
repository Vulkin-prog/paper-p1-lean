module

public import PaperP1.Model.InfiniteColoredConditional
public import PaperP1.Asymptotics.ColoredConditionalSum

/-! # The full conditional target sum in the actual infinite colored replica space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteColoredConditionalSum

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.InfiniteColoredConditional

local instance infiniteColoredConditionalSumMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem companion_T22_7 (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
      ∀ (κ : Type*) [Fintype κ], ∀ Y : ℕ, ∀ color : Option (Fin s) → κ,
      ∀ b : Fin s → Fin L → F₂,
      0 < (InfiniteColoredSamples.measure κ).real {ω | sourceEvent Y L x color b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N), conditionalProbability Y L x z color b (c z)) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := ColoredConditionalSum.prescribed_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx κ _ Y color b hb c
  let M := 2 * N + L
  have hcut : ∀ i, x i + L ≤ M := by
    intro i
    have hi := (mem_Ico.mp (hx i)).2
    omega
  have hsource : 0 < CompatibleSourcePrescriptions.sourceMass
      (ColoredWindowConditional.systems M Y L x 0 color) b := by
    rwa [← source_mass_eq (z := 0) x color b hcut]
  calc
    _ = ∑ z ∈ Ico N (2 * N), ColoredWindowConditional.conditionalProbability M Y L x z color b (c z) := by
      apply sum_congr rfl
      intro z hz
      have hzb := (mem_Ico.mp hz).2
      exact conditional_eq x color b (c z) hcut (by dsimp [M]; omega)
    _ ≤ _ := hN₀ N hN L hband x hx κ Y M le_rfl color b hsource c

end PaperP1.InfiniteColoredConditionalSum
