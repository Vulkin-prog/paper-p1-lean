module

public import PaperP1.Asymptotics.DensePairActivity
public import PaperP1.Asymptotics.TwoChannelDenseProfileReduction

/-! # The actual second factorial cumulant and its two-channel profile without unproved geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairProfiles

open PaperP1.Model

theorem uniform_profiles (C ε : ℝ) (Hmult : ℕ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ Hmult * (L + 1) →
        (|RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
          2 * PrincipalChannelEdges.beta N H L| ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
          (ChannelMainTermBounds.mainTerm N L 2 3 + ChannelMainTermBounds.mainTerm N L 3 4)| ≤
          (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨Na, _hNa, ha⟩ := DensePairActivity.uniform_activity C (ε / 2) (by positivity)
  obtain ⟨Nr, _hNr, hr⟩ := DenseNonalignedProfileReduction.uniform_bound C (ε / 2) Hmult (by positivity)
  obtain ⟨Nt, _hNt, ht⟩ := TwoChannelDenseProfileReduction.uniform_bound C (ε / 2) Hmult (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Na (max Nr (max Nt Nf))), by omega, ?_⟩
  intro N hN L H hcrit hcut hH
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdense := ha N (by omega) L hcrit
  have hcompare : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have hfinal : 2 * CompatibleActivitySplit.absolute L (DenseNonalignedProfileReduction.dense N L) +
      (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    calc
      _ ≤ 3 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [hdense, hcompare]
      _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring
  exact ⟨(hr N (by omega) L H hcrit hcut hH).trans hfinal,
    (ht N (by omega) L H hcrit hcut hH).trans hfinal⟩

end PaperP1.PairProfiles
