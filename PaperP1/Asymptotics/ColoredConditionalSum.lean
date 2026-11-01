module

public import PaperP1.Model.ColoredWindowConditional
public import PaperP1.Asymptotics.FixedSourceConditionalSum

/-! # Conditional propagation for colored prime signs, uniformly in threshold and coloring -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredConditionalSum

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ColoredPrimeSamples

local instance coloredConditionalSumTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance coloredConditionalSumMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem uniform_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
      ∀ (κ : Type*) [Fintype κ], ∀ Y M : ℕ, 2 * N + L ≤ M →
      ∀ color : Option (Fin s) → κ, ∀ a : Sample κ M, ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N), ColoredWindowConditional.mass M Y L x z color a (c z)) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := FixedSourceConditionalSum.witness_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx κ _ Y M hM color a c
  have hcut : ∀ i, x i + L ≤ M := by
    intro i
    have h := (mem_Ico.mp (hx i)).2
    omega
  have hplain := hN₀ N hN L hband x hx M hM (0 : SampleSpace M) (fun _ ↦ 0)
  simp only [map_zero] at hplain
  calc
    _ ≤ ∑ z ∈ Ico N (2 * N), WindowFamilyConditional.conditionalProbability x L (fun _ ↦ 0) z 0 := by
      apply sum_le_sum
      intro z hz
      have hzb := (mem_Ico.mp hz).2
      exact ColoredWindowConditional.infinite_homogeneous_domination x color a (c z) hcut (by omega)
    _ ≤ _ := hplain

theorem prescribed_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
      ∀ (κ : Type*) [Fintype κ], ∀ Y M : ℕ, 2 * N + L ≤ M →
      ∀ color : Option (Fin s) → κ, ∀ b : Fin s → Fin L → F₂,
      0 < CompatibleSourcePrescriptions.sourceMass (ColoredWindowConditional.systems M Y L x 0 color) b →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N), ColoredWindowConditional.conditionalProbability M Y L x z color b (c z)) ≤
          (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := uniform_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx κ _ Y M hM color b hb c
  obtain ⟨a, ha⟩ := (CompatibleSourcePrescriptions.source_mass_pos_iff _ b).mp hb
  have heq (z : ℕ) : ColoredWindowConditional.conditionalProbability M Y L x z color b (c z) =
      ColoredWindowConditional.mass M Y L x z color a (c z) :=
    ColoredWindowConditional.conditional_of_witness M Y L x z color b (c z) a ha
  simp_rw [heq]
  exact hN₀ N hN L hband x hx κ Y M hM color a c

end PaperP1.ColoredConditionalSum
