module

public import PaperP1.Analysis.QuadraticRelativeError
public import PaperP1.Arithmetic.DeterminantIntervalPartition

/-! # The original solution quadruples lie close to the coefficient-scaled quadratic grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualVerticalGrid

open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
  PaperP1.DeterminantRelativeChart PaperP1.ActualRelativeDeterminant

def ratioScale (c₁ c₂ D E : ℝ) : ℝ := (c₁ / c₂) * (D / E) ^ 2

def gridCenter (M k : ℕ) (c₁ c₂ D E : ℝ) : ℝ :=
  ratioScale c₁ c₂ D E * ((PaperP1.QuadraticIntervalGrid.grid M k : ℝ) / M)

theorem center_identity (M k : ℕ) (c₁ c₂ D E : ℝ) :
    center c₁ c₂ (intervalCenter M D E k) = ratioScale c₁ c₂ D E * ((k : ℝ) / M) ^ 2 := by
  unfold center intervalCenter ratioScale
  ring

theorem actual_grid_error (M : ℕ) (hM : 4 ≤ M) {D E c₁ c₂ h N ρ : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hN : 0 < N) (hρ : 0 < ρ) (hMh : (M : ℝ) * |h| ≤ N)
    (p : Quad) (hdlo : D ≤ p.1.1) (hdhi : (p.1.1 : ℝ) ≤ 2 * D)
    (helo : E ≤ p.1.2) (hehi : (p.1.2 : ℝ) ≤ 2 * E) (hu : 0 < p.2.1)
    (hsource : ρ * N ≤ source c₁ p.1.1 p.2.1)
    (heq : c₂ * (p.1.2 : ℝ) ^ 2 * p.2.2 = c₁ * (p.1.1 : ℝ) ^ 2 * p.2.1 + h) :
    |secondRatio p - gridCenter M (intervalIndex M D E p.1.1 p.1.2) c₁ c₂ D E| ≤
      ratioScale c₁ c₂ D E * (49 + 16 / ρ) / M := by
  let k := intervalIndex M D E p.1.1 p.1.2
  let s₀ := intervalCenter M D E k
  have hMp : 0 < M := by omega
  have hbounds := center_bounds M hM hD hE hdlo hdhi helo hehi
  have hs₀ : 0 < s₀ := (div_pos hD (by positivity : 0 < 4 * E)).trans_le hbounds.1
  have he : 0 < p.1.2 := by exact_mod_cast hE.trans_le helo
  have ha : |relativeAlpha s₀ p| ≤ 4 / M := alpha_absolute_bound M hM hD hE hdlo hdhi helo hehi
  have hmR : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have ha1 : |relativeAlpha s₀ p| ≤ 1 :=
    ha.trans ((div_le_one (by linarith : (0 : ℝ) < M)).mpr hmR)
  have hb : |relativeError c₁ c₂ h s₀ p| ≤ 4 * |h| / (ρ * N) :=
    error_bound_at_scale hc₁ hc₂ (hD.trans_le hdlo) (hE.trans_le helo)
      (by exact_mod_cast hu) hs₀ hN hρ hsource ha1
  have hbM := PaperP1.QuadraticRelativeError.beta_at_interval_scale M hMp hN hρ hMh hb
  have ht := second_normalization p hc₁ hc₂ hs₀ he hu heq
  rw [center_identity] at ht
  exact PaperP1.QuadraticRelativeError.relative_grid_error M k hM
    (index_bounds M hM hD hE hdlo hdhi helo hehi).2 (by unfold ratioScale; positivity) hρ ha hbM ht

end PaperP1.ActualVerticalGrid
