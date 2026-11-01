module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Precise ranges for the quadratic-kernel exponent comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticKernelExponents

def exponent (β δ : ℝ) : ℝ := min (β - δ) (max (β / 2 - δ) (1 - β / 2))
def capped (β δ : ℝ) : ℝ := min 1 (exponent β δ)
def affine (β δ : ℝ) : ℝ := 1 / 2 + β / 4 - δ / 2

theorem capped_le_affine (β δ : ℝ) : capped β δ ≤ affine β δ := by
  unfold capped exponent affine
  rcases le_total 1 (β - δ) with ha | ha
  · rw [max_eq_left (by linarith : 1 - β / 2 ≤ β / 2 - δ)]
    have h1 := min_le_left (1 : ℝ) (min (β - δ) (β / 2 - δ))
    have h2 := (min_le_right (1 : ℝ) (min (β - δ) (β / 2 - δ))).trans
      (min_le_right (β - δ) (β / 2 - δ))
    linarith
  · rw [max_eq_right (by linarith : β / 2 - δ ≤ 1 - β / 2)]
    have h1 := (min_le_right (1 : ℝ) (min (β - δ) (1 - β / 2))).trans
      (min_le_left (β - δ) (1 - β / 2))
    have h2 := (min_le_right (1 : ℝ) (min (β - δ) (1 - β / 2))).trans
      (min_le_right (β - δ) (1 - β / 2))
    linarith

theorem exponent_le_affine_of_range (β δ : ℝ) (hrange : β - 2 * δ ≤ 2) :
    exponent β δ ≤ affine β δ := by
  unfold exponent affine
  rcases le_total 1 (β - δ) with ha | ha
  · rw [max_eq_left (by linarith : 1 - β / 2 ≤ β / 2 - δ)]
    have h := min_le_right (β - δ) (β / 2 - δ)
    linarith
  · rw [max_eq_right (by linarith : β / 2 - δ ≤ 1 - β / 2)]
    have h1 := min_le_left (β - δ) (1 - β / 2)
    have h2 := min_le_right (β - δ) (1 - β / 2)
    linarith

theorem exponent_le_affine (β δ : ℝ) (hβ : β ≤ 2) (hδ : 0 ≤ δ) :
    exponent β δ ≤ affine β δ :=
  exponent_le_affine_of_range β δ (by linarith)

theorem exponent_le_affine_with_margin (β δ η : ℝ) (hη : 0 ≤ η)
    (hrange : β - 2 * δ ≤ 2 + η) : exponent β δ ≤ affine β δ + η / 4 := by
  unfold exponent affine
  rcases le_total 1 (β - δ) with ha | ha
  · rw [max_eq_left (by linarith : 1 - β / 2 ≤ β / 2 - δ)]
    have hb := min_le_right (β - δ) (β / 2 - δ)
    linarith
  · rw [max_eq_right (by linarith : β / 2 - δ ≤ 1 - β / 2)]
    have h1 := min_le_left (β - δ) (1 - β / 2)
    have h2 := min_le_right (β - δ) (1 - β / 2)
    linarith

theorem unrestricted_comparison_counterexample :
    affine (5 / 2) 0 < exponent (5 / 2) 0 := by
  norm_num [affine, exponent]

end PaperP1.QuadraticKernelExponents
