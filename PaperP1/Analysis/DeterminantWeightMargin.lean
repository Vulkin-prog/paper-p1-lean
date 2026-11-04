module

public import PaperP1.Analysis.DeterminantEffectiveHeights

/-! # Explicit stability of the sharp determinant margin under logarithmic scale errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantWeightMargin

theorem product_perturbation {a₀ b₀ a b C ε : ℝ}
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (ha : a₀ ≤ a) (hb : b₀ ≤ b)
    (haC : a ≤ C) (hbC : b ≤ C) (hε : 0 ≤ ε) (haε : a ≤ a₀ + ε) (hbε : b ≤ b₀ + ε) :
    a * b ≤ a₀ * b₀ + 2 * C * ε := by
  have h₁ := mul_le_mul_of_nonneg_right haε (hb₀.trans hb)
  have h₂ := mul_le_mul_of_nonneg_left hbε ha₀
  have h₃ := mul_le_mul_of_nonneg_right (add_le_add (ha.trans haC) hbC) hε
  nlinarith only [h₁, h₂, h₃]

theorem weights_product_lower {σ τ θ a₀ b₀ ζ : ℝ}
    (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hθ : 0 ≤ θ)
    (hτ : 1 - θ ≤ τ) (hσlower : (9 / 8 : ℝ) * a₀ * b₀ + ζ ≤ σ) :
    (9 / 8 : ℝ) * a₀ * b₀ + ζ - θ ≤ σ * τ := by
  have h₁ := mul_le_mul_of_nonneg_left hτ hσ
  have h₂ := mul_le_mul_of_nonneg_right hσ₁ hθ
  nlinarith only [h₁, h₂, hσlower]

theorem additive_margin {a₀ b₀ a b C ε σ τ θ ζ : ℝ}
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (ha : a₀ ≤ a) (hb : b₀ ≤ b)
    (haC : a ≤ C) (hbC : b ≤ C) (hε : 0 ≤ ε) (haε : a ≤ a₀ + ε) (hbε : b ≤ b₀ + ε)
    (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hθ : 0 ≤ θ) (hτ : 1 - θ ≤ τ)
    (hσlower : (9 / 8 : ℝ) * a₀ * b₀ + ζ ≤ σ)
    (herror : (9 / 4 : ℝ) * C * ε + θ ≤ ζ / 2) :
    (9 / 8 : ℝ) * a * b + ζ / 2 ≤ σ * τ := by
  have hp := product_perturbation ha₀ hb₀ ha hb haC hbC hε haε hbε
  have hw := weights_product_lower hσ hσ₁ hθ hτ hσlower
  nlinarith only [hp, hw, herror]

theorem multiplicative_margin {a b C η ζ σ τ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haC : a ≤ C) (hbC : b ≤ C) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hbase : (9 / 8 : ℝ) * a * b + ζ ≤ σ * τ)
    (hmargin : (27 / 8 : ℝ) * η * C ^ 2 ≤ ζ) :
    (9 / 8 : ℝ) * (1 + η) ^ 2 * a * b ≤ σ * τ := by
  have hab := mul_le_mul haC hbC hb (ha.trans haC)
  have heta := mul_nonneg hη (sub_nonneg.mpr hη₁)
  have hs : (1 + η) ^ 2 ≤ 1 + 3 * η := by nlinarith only [heta]
  have h₁ := mul_le_mul_of_nonneg_right hs (show 0 ≤ (9 / 8 : ℝ) * (a * b) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hab (show 0 ≤ (27 / 8 : ℝ) * η by positivity)
  nlinarith only [h₁, h₂, hbase, hmargin]

theorem exists_fixed_errors (C ζ : ℝ) (hC : 0 < C) (hζ : 0 < ζ) :
    ∃ ε θ η : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < η ∧ η ≤ 1 ∧
      (9 / 4 : ℝ) * C * ε + θ ≤ ζ / 4 ∧ (27 / 8 : ℝ) * η * C ^ 2 ≤ ζ / 4 := by
  let ε := min 1 (ζ / (36 * C))
  let θ := min (1 / 4) (ζ / 8)
  let η := min 1 (ζ / (18 * C ^ 2))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hζ (by positivity))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hζ (by norm_num))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hζ (by positivity))
  have he := (le_div_iff₀ (by positivity : 0 < 36 * C)).mp (min_le_right 1 (ζ / (36 * C)))
  have ht := min_le_right (1 / 4 : ℝ) (ζ / 8)
  have hn := (le_div_iff₀ (by positivity : 0 < 18 * C ^ 2)).mp (min_le_right 1 (ζ / (18 * C ^ 2)))
  refine ⟨ε, θ, η, hε, min_le_left _ _, hθ, min_le_left _ _, hη, min_le_left _ _, ?_, ?_⟩
  · change ε * (36 * C) ≤ ζ at he
    change θ ≤ ζ / 8 at ht
    linarith only [he, ht, hζ]
  · change η * (18 * C ^ 2) ≤ ζ at hn
    nlinarith only [hn, hζ]

end PaperP1.DeterminantWeightMargin
