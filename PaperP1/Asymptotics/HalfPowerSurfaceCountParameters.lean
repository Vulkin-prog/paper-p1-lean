module

public import PaperP1.Arithmetic.UniformOrdinarySurfaceCover

/-! # Uniform exponent choices for a source height N^D and a curve degree at least 2D -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfPowerSurfaceCountParameters

theorem parameters (D : ℕ) (ε : ℝ) (hD : 0 < D) (hε : 0 < ε) :
    ∃ (k : ℕ) (δ : ℝ), 2 ≤ k ∧ 0 < δ ∧ ∀ l ≥ k,
      (D : ℝ) * (2 / Real.sqrt ((2 : ℝ) ^ l) + δ) ≤ 1 / 2 + ε ∧
      (D : ℝ) * ((1 / Real.sqrt ((2 : ℝ) ^ l) + δ) + (1 / (2 * (D : ℝ)) + δ)) ≤ 1 / 2 + ε := by
  obtain ⟨E, k, δ, hE, hk, hδ, hbound⟩ := UniformOrdinarySurfaceCover.subpower_parameters (D : ℝ) ε
    (Nat.cast_nonneg D) hε
  refine ⟨k, δ, by nlinarith, hδ, ?_⟩
  intro l hl
  obtain ⟨hfirst, hsecond⟩ := hbound l hl
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hhalf : (D : ℝ) * (1 / (2 * (D : ℝ))) = 1 / 2 := by field_simp
  have hnonneg : (0 : ℝ) ≤ (D : ℝ) / ((E : ℝ) + 1) := by positivity
  constructor
  · have heq : (D : ℝ) * (2 / Real.sqrt ((2 : ℝ) ^ l) + δ) =
        2 * (D : ℝ) / Real.sqrt ((2 : ℝ) ^ l) + (D : ℝ) * δ := by ring
    rw [heq]
    linarith
  · have heq : (D : ℝ) * ((1 / Real.sqrt ((2 : ℝ) ^ l) + δ) + (1 / (2 * (D : ℝ)) + δ)) =
        (D : ℝ) / Real.sqrt ((2 : ℝ) ^ l) + 2 * (D : ℝ) * δ + 1 / 2 := by
      calc
        _ = (D : ℝ) / Real.sqrt ((2 : ℝ) ^ l) + 2 * (D : ℝ) * δ + (D : ℝ) * (1 / (2 * (D : ℝ))) := by ring
        _ = _ := by rw [hhalf]
    rw [heq]
    linarith

end PaperP1.HalfPowerSurfaceCountParameters
