module

public import PaperP1.Asymptotics.ActualPairPhase

/-! # Internal simultaneous absolute errors for both literal moving pair phases -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPairPhase

open Model FiniteChannelHierarchy ChannelMassPhaseEquivalent ActualPairPhase

theorem uniform_errors (C : ℝ) : ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < phaseMass N L 3 ∧ 0 < phaseMass N L 4 ∧
      |alpha N L - phaseMass N L 3| ≤ ε * phaseMass N L 3 ∧
      |(alpha N L - ChannelMainTermBounds.mainTerm N L 2 3) - phaseMass N L 4| ≤
        ε * phaseMass N L 4 := by
  intro ε hε
  obtain ⟨N₀, hN₀, h⟩ := uniform_phases C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hP, hQ, hfirst, hsecond⟩ := h N hN L hband
  have convert_error (A P : ℝ) (hP : 0 < P) (hh : |A / P - 1| ≤ ε) :
      |A - P| ≤ ε * P := by
    have he : A / P - 1 = (A - P) / P := by field_simp
    rw [he, abs_div, abs_of_pos hP] at hh
    exact (div_le_iff₀ hP).mp hh
  exact ⟨hP, hQ, convert_error _ _ hP hfirst, convert_error _ _ hQ hsecond⟩

end PaperP1.FixedPairPhase
