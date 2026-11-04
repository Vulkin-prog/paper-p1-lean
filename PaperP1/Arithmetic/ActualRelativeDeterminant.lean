module

public import PaperP1.Analysis.DeterminantUniformMargin
public import PaperP1.Arithmetic.DeterminantAuxiliaryBiform

/-! # Exact relative charts and determinant casts for the original integer quadruples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualRelativeDeterminant

open Finset PaperP1.DeterminantIntegerRows PaperP1.TwoKernelDeterminantBoxes
  PaperP1.DeterminantRelativeChart

def firstRatio (p : Quad) : ℝ := (p.1.1 : ℝ) / p.1.2
def secondRatio (p : Quad) : ℝ := (p.2.2 : ℝ) / p.2.1
def relativeAlpha (s₀ : ℝ) (p : Quad) : ℝ := alpha p.1.1 p.1.2 s₀
def relativeError (c₁ c₂ h s₀ : ℝ) (p : Quad) : ℝ := error c₁ c₂ p.1.2 p.2.1 h s₀

theorem first_normalization (p : Quad) {s₀ : ℝ} (hs₀ : 0 < s₀) (he : 0 < p.1.2) :
    firstRatio p = s₀ * (1 + relativeAlpha s₀ p) := by
  have heR : (p.1.2 : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  unfold firstRatio relativeAlpha alpha
  field_simp
  ring

theorem center_positive {c₁ c₂ s₀ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs₀ : 0 < s₀) :
    0 < center c₁ c₂ s₀ := by unfold center; positivity

theorem second_normalization (p : Quad) {c₁ c₂ h s₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs₀ : 0 < s₀) (he : 0 < p.1.2) (hu : 0 < p.2.1)
    (heq : c₂ * (p.1.2 : ℝ) ^ 2 * p.2.2 = c₁ * (p.1.1 : ℝ) ^ 2 * p.2.1 + h) :
    secondRatio p = center c₁ c₂ s₀ *
      (1 + 2 * relativeAlpha s₀ p + (relativeAlpha s₀ p) ^ 2 + relativeError c₁ c₂ h s₀ p) := by
  have heR : (p.1.2 : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have huR : (p.2.1 : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hh := exact_chart hc₁.ne' hc₂.ne' heR huR hs₀.ne' heq
  have ht₀ := center_positive hc₁ hc₂ hs₀
  simpa only [secondRatio, relativeAlpha, relativeError, mul_comm] using (div_eq_iff ht₀.ne').mp hh

theorem rational_matrix_cast (A B : ℕ) (P : Exponent A B → Quad) :
    (((rationalMatrix A B P).det : ℚ) : ℝ) =
      (Matrix.of (fun i j : Exponent A B ↦ firstRatio (P i) ^ j.1.val * secondRatio (P i) ^ j.2.val)).det := by
  rw [Rat.cast_det]
  congr 1
  ext i j
  simp only [rationalMatrix, rationalEntry, Matrix.map_apply, Matrix.of_apply, firstRatio, secondRatio]
  push_cast
  rfl

theorem rational_denominator_cast (A B : ℕ) (P : Exponent A B → Quad) :
    (((∏ i, denominator A B (P i)) : ℚ) : ℝ) =
      ∏ i, (P i).1.2 ^ A * ((P i).2.1 : ℝ) ^ B := by
  simp only [denominator]
  push_cast
  rfl

theorem small_of_real_small (A B : ℕ) (P : Exponent A B → Quad)
    (hsmall :
      |(Matrix.of (fun i j : Exponent A B ↦ firstRatio (P i) ^ j.1.val * secondRatio (P i) ^ j.2.val)).det| *
        (∏ i, (P i).1.2 ^ A * ((P i).2.1 : ℝ) ^ B) < 1) :
    |(rationalMatrix A B P).det| * (∏ i, denominator A B (P i)) < 1 := by
  have hh : (((|(rationalMatrix A B P).det| * (∏ i, denominator A B (P i))) : ℚ) : ℝ) < 1 := by
    rw [Rat.cast_mul, Rat.cast_abs, rational_matrix_cast, rational_denominator_cast]
    exact hsmall
  exact_mod_cast hh

end PaperP1.ActualRelativeDeterminant
