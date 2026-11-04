module

public import PaperP1.Analysis.DeterminantBoxScales

/-! # One fixed effective-height comparison constant for every occupied source chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantFixedInflation

open PaperP1.DeterminantRelativeChart

def inflation (ρ C : ℝ) : ℝ := 16 * C / ρ

theorem source_comparisons_order {ρ C N F : ℝ} (hN : 0 < N)
    (hlo : ρ * N ≤ F) (hhi : F ≤ C * N) : ρ ≤ C := by
  exact (mul_le_mul_iff_of_pos_right hN).mp (hlo.trans hhi)

theorem inflation_ge_sixteen {ρ C : ℝ} (hρ : 0 < ρ) (horder : ρ ≤ C) :
    16 ≤ inflation ρ C := by
  apply (le_div_iff₀ hρ).mpr
  nlinarith only [horder]

theorem effective_products {c₁ c₂ D E U V s₀ N ρ C : ℝ}
    (hc₂ : 0 < c₂) (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V)
    (hN : 0 < N) (hρ : 0 < ρ) (hC : 0 < C)
    (hFlo : ρ * N ≤ c₁ * D ^ 2 * U) (hFhi : c₁ * D ^ 2 * U ≤ C * N)
    (hGlo : ρ * N ≤ c₂ * E ^ 2 * V) (hGhi : c₂ * E ^ 2 * V ≤ C * N)
    (hslo : D / (4 * E) ≤ s₀) (hshi : s₀ ≤ 2 * D / E) :
    (D * E ≤ (2 * E) ^ 2 * s₀ ∧ (2 * E) ^ 2 * s₀ ≤ inflation ρ C ^ 3 * (D * E)) ∧
    (U * V ≤ (inflation ρ C * U) ^ 2 * center c₁ c₂ s₀ ∧
      (inflation ρ C * U) ^ 2 * center c₁ c₂ s₀ ≤ inflation ρ C ^ 3 * (U * V)) := by
  have horder := source_comparisons_order hN hFlo hFhi
  have hK := inflation_ge_sixteen hρ horder
  have hK₀ : 0 ≤ inflation ρ C := by linarith only [hK]
  have hK₁ : 1 ≤ inflation ρ C := by linarith only [hK]
  have hK₃ : 8 ≤ inflation ρ C ^ 3 := by
    calc
      (8 : ℝ) ≤ 16 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hK 3
  have hfirst := DeterminantEffectiveHeights.first_height_bounds hE hslo hshi
  have hcent := DeterminantCenterScales.center_comparison hc₂ hD hE hU hV hN hρ hC
    hFlo hFhi hGlo hGhi hslo hshi
  have hlo : V / (inflation ρ C * U) ≤ center c₁ c₂ s₀ := by
    convert hcent.1 using 1
    unfold inflation
    field_simp
  have hhi : center c₁ c₂ s₀ ≤ inflation ρ C * V / U := by
    calc
      _ ≤ (4 * C / ρ) * (V / U) := hcent.2
      _ = (inflation ρ C * (V / U)) / 4 := by unfold inflation; ring
      _ ≤ inflation ρ C * (V / U) := div_le_self (mul_nonneg hK₀ (div_pos hV hU).le) (by norm_num)
      _ = _ := by ring
  exact ⟨⟨hfirst.1, hfirst.2.trans (mul_le_mul_of_nonneg_right hK₃ (mul_pos hD hE).le)⟩,
    DeterminantEffectiveHeights.inflated_pair_height hK₁ hU hV hlo hhi⟩

end PaperP1.DeterminantFixedInflation
