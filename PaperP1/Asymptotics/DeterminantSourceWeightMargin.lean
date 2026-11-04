module

public import PaperP1.Asymptotics.DeterminantNormalizedWeights

/-! # Uniform source-scale errors imply the required positive determinant product margin -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantSourceWeightMargin

open PaperP1.DeterminantLogScale PaperP1.DeterminantNormalizedWeights

theorem uniform_margin (δ C K Kshift A₀ ζ ρ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hK : 0 < K) (hζ : 0 < ζ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ M : ℕ, ∀ h D E U V X Y : ℝ,
      0 < M → M ≤ N → 0 < D → 0 < E → 0 < U → 0 < V →
      1 ≤ h → h ≤ Kshift * (Real.log N) ^ A₀ →
      (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) ≤ M →
      δ * Real.log N ≤ Real.log (D * E) → Real.log (D * E) ≤ C * Real.log N →
      δ * Real.log N ≤ Real.log (U * V) → Real.log (U * V) ≤ C * Real.log N →
      D * E ≤ X → X ≤ K * (D * E) → U * V ≤ Y → Y ≤ K * (U * V) →
      2 ≤ N ∧
      δ ≤ Real.log X / Real.log N ∧ Real.log X / Real.log N ≤ C + 1 ∧
      δ ≤ Real.log Y / Real.log N ∧ Real.log Y / Real.log N ≤ C + 1 ∧
      0 < horizontal N M ∧ 0 < vertical N ρ h ∧ horizontal N M + vertical N ρ h ≤ 2 ∧
      (9 / 8 : ℝ) * (1 + η) ^ 2 * (Real.log X / Real.log N) * (Real.log Y / Real.log N) ≤
        horizontal N M * vertical N ρ h := by
  obtain ⟨ε, θ, η, hε, hε₁, hθ, hθ₁, hη, hη₁, herror, hmargin⟩ :=
    DeterminantWeightMargin.exists_fixed_errors (C + 1) ζ (by linarith only [hC]) hζ
  obtain ⟨NK, hNK⟩ := fixed_log_error K ε hε
  obtain ⟨N4, hN4⟩ := fixed_log_error 4 (ζ / 2) (by positivity)
  obtain ⟨Nh, hNh⟩ := vertical_polylog_uniform ρ Kshift A₀ θ hρ hθ
  refine ⟨η, hη, hη₁, max NK (max N4 Nh), ?_⟩
  intro N hN M h D E U V X Y hM hMN hD hE hU hV hh hshift hscale hPl hPu hRl hRu hXl hXu hYl hYu
  obtain ⟨hN₂, hKerror⟩ := hNK N (by omega)
  have h4error := (hN4 N (by omega)).2
  have hshiftpow := hNh N (by omega) h hshift
  have hT : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpa : δ ≤ Real.log (D * E) / Real.log N := (le_div_iff₀ hT).mpr hPl
  have hpb : δ ≤ Real.log (U * V) / Real.log N := (le_div_iff₀ hT).mpr hRl
  have hpA : Real.log (D * E) / Real.log N ≤ C := (div_le_iff₀ hT).mpr hPu
  have hpB : Real.log (U * V) / Real.log N ≤ C := (div_le_iff₀ hT).mpr hRu
  have hax := DeterminantEffectiveHeights.normalized_log_comparison (mul_pos hD hE) hK hT hXl hXu
  have hby := DeterminantEffectiveHeights.normalized_log_comparison (mul_pos hU hV) hK hT hYl hYu
  have haε : Real.log X / Real.log N ≤ Real.log (D * E) / Real.log N + ε := by
    linarith only [hax.2, hKerror]
  have hbε : Real.log Y / Real.log N ≤ Real.log (U * V) / Real.log N + ε := by
    linarith only [hby.2, hKerror]
  have haC : Real.log X / Real.log N ≤ C + 1 := by linarith only [haε, hpA, hε₁]
  have hbC : Real.log Y / Real.log N ≤ C + 1 := by linarith only [hbε, hpB, hε₁]
  have hσlo : (9 / 8 : ℝ) * (Real.log (D * E) / Real.log N) *
      (Real.log (U * V) / Real.log N) + ζ / 2 ≤ horizontal N M := by
    have hs := horizontal_lower N M hN₂ hM D E U V ζ hscale
    linarith only [hs, h4error]
  have hpa₀ := (hδ.trans_le hpa).le
  have hpb₀ := (hδ.trans_le hpb).le
  have hσ : 0 < horizontal N M := by
    have hz : 0 ≤ (9 / 8 : ℝ) * (Real.log (D * E) / Real.log N) *
        (Real.log (U * V) / Real.log N) := by positivity
    linarith only [hσlo, hz, hζ]
  have hσ₁ := horizontal_upper N M hN₂ hM hMN
  have hhpos : 0 < h := by linarith only [hh]
  have hτlo := vertical_lower N hN₂ hρ hhpos hshiftpow
  have hτ₁ := vertical_upper N hN₂ hρ hρ₁ hh
  have hτ : 0 < vertical N ρ h := by linarith only [hτlo, hθ₁]
  have hadd : (9 / 8 : ℝ) * (Real.log X / Real.log N) * (Real.log Y / Real.log N) + ζ / 4 ≤
      horizontal N M * vertical N ρ h := by
    have ha := DeterminantWeightMargin.additive_margin hpa₀ hpb₀ hax.1 hby.1 haC hbC hε.le haε hbε
      hσ.le hσ₁ hθ.le hτlo hσlo (by linarith only [herror])
    convert ha using 1
    ring
  have hprod := DeterminantWeightMargin.multiplicative_margin
    (hpa₀.trans hax.1) (hpb₀.trans hby.1) haC hbC hη.le hη₁ hadd hmargin
  exact ⟨hN₂, hpa.trans hax.1, haC, hpb.trans hby.1, hbC, hσ, hτ,
    by linarith only [hσ₁, hτ₁], hprod⟩

end PaperP1.DeterminantSourceWeightMargin
