module

public import PaperP1.Analysis.DeterminantTwoKernelExponents
public import Mathlib.Tactic.FieldSimp

/-! # Relative determinant charts have no coefficient-ratio error loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantRelativeChart

def alpha (d e s₀ : ℝ) : ℝ := d / (e * s₀) - 1

def center (c₁ c₂ s₀ : ℝ) : ℝ := (c₁ / c₂) * s₀ ^ 2

def source (c₁ d u : ℝ) : ℝ := c₁ * d ^ 2 * u

def error (c₁ c₂ e u h s₀ : ℝ) : ℝ := h / (c₂ * e ^ 2 * u * center c₁ c₂ s₀)

theorem source_pos {c₁ d u : ℝ} (hc₁ : 0 < c₁) (hd : 0 < d) (hu : 0 < u) :
    0 < source c₁ d u := mul_pos (mul_pos hc₁ (sq_pos_of_pos hd)) hu

theorem exact_chart {c₁ c₂ d e u v h s₀ : ℝ}
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (he : e ≠ 0) (hu : u ≠ 0) (hs₀ : s₀ ≠ 0)
    (heq : c₂ * e ^ 2 * v = c₁ * d ^ 2 * u + h) :
    (v / u) / center c₁ c₂ s₀ =
      1 + 2 * alpha d e s₀ + (alpha d e s₀) ^ 2 + error c₁ c₂ e u h s₀ := by
  unfold error center alpha
  field_simp
  nlinarith only [heq]

theorem error_eq_relative_source {c₁ c₂ d e u h s₀ : ℝ}
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hu : u ≠ 0) (hs₀ : s₀ ≠ 0) :
    error c₁ c₂ e u h s₀ = (h / source c₁ d u) * (1 + alpha d e s₀) ^ 2 := by
  unfold error center source alpha
  field_simp
  ring

theorem relative_square_bound {a : ℝ} (ha : |a| ≤ 1) : (1 + a) ^ 2 ≤ 4 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha
  have hh := mul_nonneg (by linarith : 0 ≤ 1 - a) (by linarith : 0 ≤ 3 + a)
  nlinarith only [hh]

theorem alpha_le_one {d e s₀ M : ℝ} (hM : 1 ≤ M) (ha : |alpha d e s₀| ≤ 1 / M) :
    |alpha d e s₀| ≤ 1 := by
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hM
  exact ha.trans (by simpa only [one_div_one] using hh)

theorem error_bound {c₁ c₂ d e u h s₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd : 0 < d) (he : 0 < e) (hu : 0 < u) (hs₀ : 0 < s₀)
    (ha : |alpha d e s₀| ≤ 1) :
    |error c₁ c₂ e u h s₀| ≤ 4 * |h| / source c₁ d u := by
  have hn := source_pos hc₁ hd hu
  rw [error_eq_relative_source hc₁.ne' hc₂.ne' hd.ne' he.ne' hu.ne' hs₀.ne',
    abs_mul, abs_div, abs_of_pos hn, abs_of_nonneg (sq_nonneg (1 + alpha d e s₀))]
  calc
    _ ≤ (|h| / source c₁ d u) * 4 := mul_le_mul_of_nonneg_left (relative_square_bound ha)
      (div_nonneg (abs_nonneg h) hn.le)
    _ = _ := by ring

theorem error_bound_at_scale {c₁ c₂ d e u h s₀ N ρ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd : 0 < d) (he : 0 < e) (hu : 0 < u) (hs₀ : 0 < s₀)
    (hN : 0 < N) (hρ : 0 < ρ) (hsource : ρ * N ≤ source c₁ d u)
    (ha : |alpha d e s₀| ≤ 1) :
    |error c₁ c₂ e u h s₀| ≤ 4 * |h| / (ρ * N) := by
  exact (error_bound hc₁ hc₂ hd he hu hs₀ ha).trans
    (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg h)) (mul_pos hρ hN) hsource)

end PaperP1.DeterminantRelativeChart
