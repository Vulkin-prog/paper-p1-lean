module

public import PaperP1.Arithmetic.DeterminantSourceBox
public import PaperP1.Arithmetic.ActualVerticalGrid

/-! # Effective second-pair scales keep all moving coefficient dependence explicit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveSourceCoordinates

def scale (N c D : ℝ) : ℝ := N / (c * D ^ 2)

theorem scale_bounds {N c D U ρ C : ℝ} (hN : 0 < N) (hc : 1 ≤ c) (hD : 1 ≤ D)
    (hU : 1 ≤ U) (hlo : ρ * N ≤ c * D ^ 2 * U) (hhi : c * D ^ 2 * U ≤ C * N) :
    0 < scale N c D ∧ scale N c D ≤ N ∧ U ≤ C * scale N c D ∧
      ρ * scale N c D ≤ U ∧ 1 ≤ C * scale N c D := by
  have hcp : 0 < c := by linarith
  have hDp : 0 < D := by linarith
  have hden : 0 < c * D ^ 2 := by positivity
  have hden1 : 1 ≤ c * D ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg D)]
  have hupper : U ≤ C * scale N c D := by
    unfold scale
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hhi]
  have hlower : ρ * scale N c D ≤ U := by
    unfold scale
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hlo]
  exact ⟨div_pos hN hden, div_le_self hN.le hden1, hupper, hlower, hU.trans hupper⟩

theorem ratio_identity {N c₁ c₂ D E : ℝ} (hN : N ≠ 0) (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hD : D ≠ 0) (hE : E ≠ 0) :
    scale N c₂ E / scale N c₁ D = PaperP1.ActualVerticalGrid.ratioScale c₁ c₂ D E := by
  unfold scale PaperP1.ActualVerticalGrid.ratioScale
  field_simp

end PaperP1.EffectiveSourceCoordinates
