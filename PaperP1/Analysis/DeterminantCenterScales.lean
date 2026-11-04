module

public import PaperP1.Arithmetic.DeterminantIntervalPartition

/-! # Moving coefficients cancel from the actual local-center scale comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantCenterScales

open PaperP1.DeterminantRelativeChart

theorem source_ratio_bounds {F G N ρ C : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (hC : 0 < C)
    (hFlo : ρ * N ≤ F) (hFhi : F ≤ C * N) (hGlo : ρ * N ≤ G) (hGhi : G ≤ C * N) :
    ρ / C ≤ F / G ∧ F / G ≤ C / ρ := by
  have hF : 0 < F := (mul_pos hρ hN).trans_le hFlo
  have hG : 0 < G := (mul_pos hρ hN).trans_le hGlo
  constructor
  · apply (div_le_div_iff₀ hC hG).mpr
    have h₁ := mul_le_mul_of_nonneg_left hGhi hρ.le
    have h₂ := mul_le_mul_of_nonneg_left hFlo hC.le
    nlinarith only [h₁, h₂]
  · apply (div_le_div_iff₀ hG hρ).mpr
    have h₁ := mul_le_mul_of_nonneg_left hFhi hρ.le
    have h₂ := mul_le_mul_of_nonneg_left hGlo hC.le
    nlinarith only [h₁, h₂]

theorem normalized_center_bounds {D E s₀ : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hlo : D / (4 * E) ≤ s₀) (hhi : s₀ ≤ 2 * D / E) :
    (1 / 4 : ℝ) ≤ s₀ * E / D ∧ s₀ * E / D ≤ 2 := by
  have h₁ := (div_le_iff₀ (by positivity : 0 < 4 * E)).mp hlo
  have h₂ := (le_div_iff₀ hE).mp hhi
  constructor
  · apply (le_div_iff₀ hD).mpr
    nlinarith only [h₁]
  · apply (div_le_iff₀ hD).mpr
    exact h₂

theorem center_ratio_identity {c₁ c₂ D E U V s₀ : ℝ}
    (hc₂ : c₂ ≠ 0) (hD : D ≠ 0) (hE : E ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0) :
    center c₁ c₂ s₀ / (V / U) =
      (c₁ * D ^ 2 * U / (c₂ * E ^ 2 * V)) * (s₀ * E / D) ^ 2 := by
  unfold center
  field_simp

theorem center_comparison {c₁ c₂ D E U V s₀ N ρ C : ℝ}
    (hc₂ : 0 < c₂) (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hN : 0 < N) (hρ : 0 < ρ) (hC : 0 < C)
    (hFlo : ρ * N ≤ c₁ * D ^ 2 * U) (hFhi : c₁ * D ^ 2 * U ≤ C * N)
    (hGlo : ρ * N ≤ c₂ * E ^ 2 * V) (hGhi : c₂ * E ^ 2 * V ≤ C * N)
    (hslo : D / (4 * E) ≤ s₀) (hshi : s₀ ≤ 2 * D / E) :
    (ρ / (16 * C)) * (V / U) ≤ center c₁ c₂ s₀ ∧
      center c₁ c₂ s₀ ≤ (4 * C / ρ) * (V / U) := by
  have hratio := source_ratio_bounds hN hρ hC hFlo hFhi hGlo hGhi
  have hs := normalized_center_bounds hD hE hslo hshi
  have hs₀ : 0 ≤ s₀ * E / D := by linarith only [hs.1]
  have hslo' : (1 / 16 : ℝ) ≤ (s₀ * E / D) ^ 2 := by nlinarith only [hs.1]
  have hshi' : (s₀ * E / D) ^ 2 ≤ 4 := by nlinarith only [hs₀, hs.2]
  have hleft := mul_le_mul hratio.1 hslo' (by norm_num : (0 : ℝ) ≤ 1 / 16) ((div_nonneg hρ.le hC.le).trans hratio.1)
  have hright := mul_le_mul hratio.2 hshi' (sq_nonneg _) (div_nonneg hC.le hρ.le)
  have hident := center_ratio_identity (c₁ := c₁) (s₀ := s₀) hc₂.ne' hD.ne' hE.ne' hU.ne' hV.ne'
  have hlo : ρ / (16 * C) ≤ center c₁ c₂ s₀ / (V / U) := by
    rw [hident]
    convert hleft using 1
    ring
  have hhi : center c₁ c₂ s₀ / (V / U) ≤ 4 * C / ρ := by
    rw [hident]
    convert hright using 1
    ring
  exact ⟨(le_div_iff₀ (div_pos hV hU)).mp hlo, (div_le_iff₀ (div_pos hV hU)).mp hhi⟩

end PaperP1.DeterminantCenterScales
