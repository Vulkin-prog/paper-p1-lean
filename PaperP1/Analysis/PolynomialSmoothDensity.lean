module

public import PaperP1.Analysis.ExponentialSmoothLower

/-! # Positive global density of ordinary smooth integers at every fixed power cutoff

The internal prime bands and finite density induction supply an explicit
positive density depending on the fixed exponent. No short-interval theorem
or Dickman asymptotic is assumed or asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialSmoothDensity

open Filter OrdinarySmoothCensus SaddleParameters SaddleScales

theorem uniform_lower (α : ℝ) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      δ * (N : ℝ) ≤ (smoothUpTo N ⌊(N : ℝ) ^ α⌋₊).card := by
  obtain ⟨b, hb, H₀, hl⟩ := ExponentialSmoothLower.uniform_lower (1 / 2) (by norm_num) (by norm_num)
  let β := min α (1 / b)
  have hβ : 0 < β := lt_min hα (by positivity)
  have hβα : β ≤ α := min_le_left _ _
  have hbβ : b * β ≤ 1 := by
    have hh := (le_div_iff₀ hb).mp (min_le_right α (1 / b))
    nlinarith only [hh]
  let r := b * β / 2
  let k := ⌈1 / ((1 / 2 : ℝ) * β)⌉₊
  let δ := r ^ k
  have hr : 0 < r := by dsimp only [r]; positivity
  have hδ : 0 < δ := pow_pos hr _
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hh⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop (H₀ / β)))
  refine ⟨δ, hδ, N₀, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hH : H₀ ≤ β * Real.log N := by
    have hx := (div_le_iff₀ hβ).mp (hh N (by omega))
    change H₀ ≤ Real.log N * β at hx
    nlinarith only [hx]
  have hsmall : b * (β * Real.log N) ≤ 2 * Real.log N := by
    have hx := mul_le_mul_of_nonneg_right hbβ hlog.le
    nlinarith only [hx, hlog]
  have hbound := (hl (β * Real.log N) hH N (by omega) hsmall).1
  have hrid : b * (β * Real.log N) / (2 * Real.log N) = r := by
    dsimp only [r]
    field_simp
  have hkid : Real.log N / ((1 / 2 : ℝ) * (β * Real.log N)) = 1 / ((1 / 2 : ℝ) * β) := by
    field_simp
  rw [hrid, hkid] at hbound
  have hcut : ⌊Real.exp (β * Real.log N)⌋₊ ≤ ⌊(N : ℝ) ^ α⌋₊ := by
    apply Nat.floor_le_floor
    calc
      _ = (N : ℝ) ^ β := by rw [Real.rpow_def_of_pos hn]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hβα
  have hc := Finset.card_le_card (smoothUpTo_mono (le_refl N) hcut)
  change (N : ℝ) * δ ≤ (smoothUpTo N ⌊Real.exp (β * Real.log N)⌋₊).card at hbound
  have hcR : ((smoothUpTo N ⌊Real.exp (β * Real.log N)⌋₊).card : ℝ) ≤
      (smoothUpTo N ⌊(N : ℝ) ^ α⌋₊).card := by exact_mod_cast hc
  nlinarith only [hbound, hcR]

end PaperP1.PolynomialSmoothDensity
