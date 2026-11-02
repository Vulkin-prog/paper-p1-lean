module

public import PaperP1.Model.SharedPrincipalEdgePairs
public import PaperP1.Asymptotics.SharedPrincipalTripleMass

/-! # The complete actual overlapping contribution to the principal-edge second factorial moment is negligible -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPrincipalEdgePairMass

open PaperP1.SharedPrincipalEdgePairs PaperP1.PrincipalChannelEdges

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → contribution N H L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := SharedPrincipalTripleMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 9 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NM (max NG NA)), by omega, ?_⟩
  intro N hN L H hband
  calc
    contribution N H L ≤ 9 * SharedPrincipalTriples.mass N H L :=
      contribution_le_mass (by omega) (hg N (by omega) L hband).2
    _ ≤ 9 * (N : ℝ) ^ (-41 / 30 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L H hband) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem relative_to_beta_squared (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      contribution N H L ≤ δ * beta N H L ^ 2 := by
  obtain ⟨NM, _hNM, hm⟩ := SharedPrincipalTripleMass.relative_to_beta_squared C D (δ / 9) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NM NG), by omega, ?_⟩
  intro N hN L H hband hcut hH
  calc
    contribution N H L ≤ 9 * SharedPrincipalTriples.mass N H L :=
      contribution_le_mass (by omega) (hg N (by omega) L hband).2
    _ ≤ 9 * ((δ / 9) * beta N H L ^ 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L H hband hcut hH) (by norm_num)
    _ = _ := by ring

end PaperP1.SharedPrincipalEdgePairMass
