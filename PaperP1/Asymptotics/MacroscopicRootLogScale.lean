module

public import PaperP1.Asymptotics.MacroscopicIntervalGeometry

/-! # Critical word scales transported to each individual macroscopic source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicRootLogScale

open PaperP1.CriticalBandScale PaperP1.MacroscopicIntervalGeometry

theorem root_band (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ x ∈ starts M δ,
      lowerScale * Real.log x ≤ ((L + 1 : ℕ) : ℝ) ∧
        ((L + 1 : ℕ) : ℝ) ≤ (upperScale / δ) * Real.log x := by
  obtain ⟨M₀, h⟩ := critical_band_scale C
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit x hx
  obtain ⟨hlo, hhi⟩ := h M (by omega) L hcrit
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by
    have := starts_pos (by omega : 2 ≤ M) hδ hx
    omega)
  have hloghi := Real.log_le_log hxpos
    (show (x : ℝ) ≤ M by exact_mod_cast (mem_starts_iff.mp hx).2.le)
  have hloglo := log_lower (by omega : 2 ≤ M) hx
  constructor
  · exact (mul_le_mul_of_nonneg_left hloghi lowerScale_pos.le).trans hlo
  · calc
      _ ≤ upperScale * Real.log M := hhi
      _ = (upperScale / δ) * (δ * Real.log M) := by field_simp [hδ.ne']
      _ ≤ (upperScale / δ) * Real.log x :=
        mul_le_mul_of_nonneg_left hloglo (div_nonneg upperScale_pos.le hδ.le)

end PaperP1.MacroscopicRootLogScale
