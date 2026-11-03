module

public import PaperP1.Asymptotics.RetainedGoodPairMass
public import PaperP1.Asymptotics.SecondFactorialCorrectionLower

/-! # The actual good-pair joint parameter is bounded by the nominal correction scale without geometric input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedGoodPairScale

open PaperP1.RetainedReferenceTheorem

theorem uniform_bound (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      beta H N L ≤ K * SecondFactorialCorrection.value N L := by
  obtain ⟨K, hK, NK, _hNK, hk⟩ := HomogeneousChannelMass.uniform_principal_upper C
  obtain ⟨c, hc, NC, _hNC, hh⟩ := SecondFactorialCorrectionLower.uniform_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨K / c, div_pos hK hc, 10 + NK + NC + NG, by omega, ?_⟩
  intro N hN L hband H
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  calc
    _ ≤ PrimitiveNominalMass.mass (HomogeneousChannelMass.rawPrincipal N 0 L) L :=
      RetainedGoodPairMass.beta_le_raw (by omega) hL H
    _ ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) := hk N (by omega) L 0 hband
    _ = (K / c) * (c * L * (N : ℝ) ^ (-2 / 3 : ℝ)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hh N (by omega) L hband) (div_pos hK hc).le

end PaperP1.RetainedGoodPairScale
