module

public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # A common critical threshold for every offset radius up to D times the width -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedOffsetRegime

theorem uniform_widths (C : ℝ) (D : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W ≤ D * (L + 1) →
      W ≤ (L + 1) ^ 2 ∧ 2 * W ≤ (L + 1) ^ 3 ∧ W < N := by
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C (2 * D + 2)
  obtain ⟨Np, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C (D : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max Ng Np, ?_⟩
  intro N hN L W hcrit hW
  have hB := (hg N (by omega) L hcrit).2.1
  have htwo : 2 ≤ L + 1 := (hg N (by omega) L hcrit).2.2.1
  have hprod : (2 * D) * (L + 1) ≤ (L + 1) * (L + 1) :=
    Nat.mul_le_mul_right (L + 1) (by omega)
  have hsq : 2 * W ≤ (L + 1) ^ 2 := by nlinarith only [hW, hprod]
  have hcube : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsmall : D * (L + 1) < N := by
    have hh := hp N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  exact ⟨by omega, hsq.trans hcube, hW.trans_lt hsmall⟩

end PaperP1.EnlargedOffsetRegime
