module

public import PaperP1.Asymptotics.LogFifthPivotCutoff
public import PaperP1.Asymptotics.AnchoredObstructionUnderOrdinaryCensus

/-! # The exact printed cutoff and nominal scale of the anchor obstruction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrintedAnchorObstructionParameters

open Filter PaperP1.LogFifthPivotCutoff

theorem uniform_parameters (C D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      1 ≤ L ∧ 2 * (L + E + 2) ≤ cutoff N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨NC, hC⟩ := uniform_data D 1 zero_lt_one le_rfl
  obtain ⟨NL, hL⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop ((C + 1) * Real.log 2)))
  refine ⟨max NC NL, ?_⟩
  intro N hN L E hband hwidth
  have hlarge : C + 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hlog2).mpr (hL N (by omega))
  have hlo := (abs_le.mp hband).1
  have hlength : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ L by linarith only [hlarge, hlo])
  exact ⟨hlength, (hC N (by omega) (L + E + 2) 0 hwidth (by omega)).1⟩

def nominal (N L i : ℕ) (a : ℝ) : ℝ :=
  (2 ^ (2 * i) : ℝ)⁻¹ * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ 2 * (N : ℝ) ^ (-a)

theorem nominal_eq {N : ℕ} (hN : 0 < N) (L i : ℕ) (a : ℝ) :
    nominal N L i a = (PaperP1.AnchoredPrivateField.rate (L + i)) ^ 2 * (N : ℝ) ^ (2 - a) :=
  (PaperP1.AnchoredObstructionUnderOrdinaryCensus.nominal_scale_identity hN L i a).symm

theorem nominal_nonneg (N L i : ℕ) (a : ℝ) : 0 ≤ nominal N L i a := by
  unfold nominal
  positivity

end PaperP1.PrintedAnchorObstructionParameters
