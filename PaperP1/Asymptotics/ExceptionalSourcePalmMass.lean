module

public import PaperP1.Model.GoodPairGeneratedTriples
public import PaperP1.Asymptotics.ConditionalNegativeDeviation

/-! # The nominal Palm mass of the actual fixed-source branching exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExceptionalSourcePalmMass

open Finset PaperP1.Model PaperP1.GoodPairGeneratedTriples

theorem uniform_bound (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ e : Finset ℕ,
      e ⊆ dyadicBlock N → e.card ≤ j →
      ((bad N L e).card : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := FixedWindowBranching.badStarts_card_critical C j (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C)
    (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max NB NA), by omega, ?_⟩
  intro N hN L hband e he hcard
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbad := hb N (by omega) L hband e he hcard
  calc
    _ ≤ (N : ℝ) ^ (1 / 2 + ε / 2) * ((2 : ℝ) ^ C / N) :=
      mul_le_mul hbad (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband)
        (by positivity) (by positivity)
    _ = (2 : ℝ) ^ C * (N : ℝ) ^ (-1 / 2 + ε / 2) := by
      rw [show -1 / 2 + ε / 2 = (1 / 2 + ε / 2) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ _ := by
      simpa only [show (-1 / 2 + ε / 2) + ε / 2 = -1 / 2 + ε by ring] using ha N (by omega)

end PaperP1.ExceptionalSourcePalmMass
