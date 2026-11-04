module

public import PaperP1.Analysis.DeterminantBoxScales
public import PaperP1.Analysis.ReducedSourceParameter

/-! # Explicit stability of the determinant exponent under changed sizes and scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantShapeStability

theorem denominator_loss (t t' A B u : ℝ) (ht : 1 ≤ t)
    (hhalf : t / 2 ≤ t') (_hle : t' ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAu : A ≤ 3 * t) (hBu : B ≤ 3 * t) (hu : 0 ≤ u) (hgap : t - t' ≤ u) :
    A * B / t' - A * B / t ≤ 18 * u := by
  have ht₀ : 0 < t := by linarith
  have ht'₀ : 0 < t' := by linarith
  have hAB : A * B ≤ 9 * t ^ 2 := by
    have hp := mul_le_mul hAu hBu hB (by positivity : 0 ≤ 3 * t)
    nlinarith only [hp]
  have hid : A * B / t' - A * B / t = (A * B * (t - t')) / (t' * t) := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (mul_pos ht'₀ ht₀)).mpr
  calc
    A * B * (t - t') ≤ A * B * u := mul_le_mul_of_nonneg_left hgap (mul_nonneg hA hB)
    _ ≤ 9 * t ^ 2 * u := mul_le_mul_of_nonneg_right hAB hu
    _ ≤ 18 * u * (t' * t) := by
      have hp := mul_nonneg (by positivity : 0 ≤ 9 * t * u) (show 0 ≤ 2 * t' - t by linarith)
      nlinarith only [hp]

theorem numerator_loss (t t' A B A' B' c : ℝ) (ht : 1 ≤ t) (hhalf : t / 2 ≤ t')
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hAu : A ≤ 3 * t) (hBu : B ≤ 3 * t)
    (_hA' : 0 ≤ A') (hB' : 0 ≤ B') (hc : 0 ≤ c) (hAA : A' ≤ A + c) (hBB : B' ≤ B + c) :
    A' * B' / t' ≤ A * B / t' + 12 * c + 2 * c ^ 2 := by
  have ht'₀ : 0 < t' := by linarith
  have hprod : A' * B' ≤ (A + c) * (B + c) :=
    mul_le_mul hAA hBB hB' (by positivity)
  have hprod' : A' * B' ≤ A * B + 6 * c * t + c ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hAu hc
    have h₂ := mul_le_mul_of_nonneg_left hBu hc
    nlinarith only [hprod, h₁, h₂]
  have hlinear := mul_nonneg hc (show 0 ≤ 2 * t' - t by linarith)
  have hquadratic := mul_nonneg (sq_nonneg c) (show 0 ≤ 2 * t' - 1 by linarith)
  apply (div_le_iff₀ ht'₀).mpr
  have hid : (A * B / t' + 12 * c + 2 * c ^ 2) * t' = A * B + (12 * c + 2 * c ^ 2) * t' := by
    field_simp
    ring
  rw [hid]
  nlinarith only [hprod', hlinear, hquadratic]

theorem weighted_loss (t t' A B A' B' c u : ℝ) (ht : 1 ≤ t)
    (hhalf : t / 2 ≤ t') (hle : t' ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAu : A ≤ 3 * t) (hBu : B ≤ 3 * t) (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (hc : 0 ≤ c) (hAA : A' ≤ A + c) (hBB : B' ≤ B + c)
    (hu : 0 ≤ u) (hgap : t - t' ≤ u) :
    (9 / 8 : ℝ) * A' * B' / t' ≤ (9 / 8 : ℝ) * A * B / t +
      (81 / 4 : ℝ) * u + (27 / 2 : ℝ) * c + (9 / 4 : ℝ) * c ^ 2 := by
  have hd := denominator_loss t t' A B u ht hhalf hle hA hB hAu hBu hu hgap
  have hn := numerator_loss t t' A B A' B' c ht hhalf hA hB hAu hBu hA' hB' hc hAA hBB
  have h₁ : (9 / 8 : ℝ) * A' * B' / t' = (9 / 8 : ℝ) * (A' * B' / t') := by ring
  have h₂ : (9 / 8 : ℝ) * A * B / t = (9 / 8 : ℝ) * (A * B / t) := by ring
  rw [h₁, h₂]
  nlinarith only [hd, hn]

theorem enlarged_le_original (D : ℝ) (g : ℕ) (hD : 1 ≤ D) (hg : 0 < g) :
    ReducedDyadicScales.enlarged D g ≤ D := by
  apply max_le hD
  apply (div_le_iff₀ (by exact_mod_cast hg : (0 : ℝ) < g)).mpr
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hg₁ (show 0 ≤ D by linarith)

theorem enlarged_log_bounds (D E : ℝ) (g : ℕ) (hD : 1 ≤ D) (hE : 1 ≤ E) (hg : 0 < g) :
    0 ≤ Real.log (ReducedDyadicScales.enlarged D g * ReducedDyadicScales.enlarged E g) ∧
      Real.log (ReducedDyadicScales.enlarged D g * ReducedDyadicScales.enlarged E g) ≤ Real.log (D * E) := by
  have hd := ReducedDyadicScales.enlarged_ge_one D g
  have he := ReducedDyadicScales.enlarged_ge_one E g
  have hp : 1 ≤ ReducedDyadicScales.enlarged D g * ReducedDyadicScales.enlarged E g := by
    nlinarith only [hd, he, mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr he)]
  refine ⟨Real.log_nonneg hp, Real.log_le_log (by linarith only [hp]) ?_⟩
  exact mul_le_mul (enlarged_le_original D g hD hg) (enlarged_le_original E g hE hg)
    (by linarith only [he]) (by linarith only [hD])

end PaperP1.DeterminantShapeStability
