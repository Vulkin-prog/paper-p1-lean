module

public import PaperP1.Analysis.DeterminantWeightMargin
public import PaperP1.Asymptotics.DeterminantHorizontalScale

/-! # Actual horizontal and polylogarithmic vertical logarithmic weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantNormalizedWeights

open PaperP1.DeterminantLogScale

def horizontal (N M : ℕ) : ℝ := Real.log ((M : ℝ) / 4) / Real.log N
def vertical (N : ℕ) (ρ h : ℝ) : ℝ := Real.log (ρ * N / (4 * h)) / Real.log N

theorem fixed_log_error (K ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N ∧ Real.log K / Real.log N ≤ ε := by
  let N₀ := max 2 ⌈Real.exp (Real.log K / ε)⌉₊
  refine ⟨N₀, ?_⟩
  intro N hN
  have hN₂ : 2 ≤ N := by dsimp [N₀] at hN; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have he : Real.log K / ε ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).mpr
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (Real.log K / ε)⌉₊ ≤ N by dsimp [N₀] at hN; omega))
  exact ⟨hN₂, (div_le_iff₀ hlog).mpr (by
    have hh := (div_le_iff₀ hε).mp he
    linarith only [hh])⟩

theorem horizontal_lower (N M : ℕ) (hN : 2 ≤ N) (hM : 0 < M) (D E U V ζ : ℝ)
    (hscale : (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) ≤ M) :
    (9 / 8 : ℝ) * (Real.log (D * E) / Real.log N) * (Real.log (U * V) / Real.log N) +
      ζ - Real.log 4 / Real.log N ≤ horizontal N M := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have ht : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hn ζ) (Real.exp_pos _)) hscale
  rw [Real.log_mul (Real.rpow_pos_of_pos hn ζ).ne' (Real.exp_pos _).ne',
    Real.log_rpow hn, Real.log_exp] at hh
  unfold horizontal
  rw [Real.log_div hm.ne' (by norm_num : (4 : ℝ) ≠ 0)]
  apply (le_div_iff₀ ht).mpr
  have heq : ((9 / 8 : ℝ) * (Real.log (D * E) / Real.log N) * (Real.log (U * V) / Real.log N) +
      ζ - Real.log 4 / Real.log N) * Real.log N =
        ζ * Real.log N + logShape N D E U V - Real.log 4 := by
    unfold logShape
    field_simp
    ring
  rw [heq]
  linarith only [hh]

theorem horizontal_upper (N M : ℕ) (hN : 2 ≤ N) (hM : 0 < M) (hMN : M ≤ N) :
    horizontal N M ≤ 1 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have ht : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  apply (div_le_one ht).mpr
  apply Real.log_le_log (div_pos hm (by norm_num))
  exact (div_le_self hm.le (by norm_num : (1 : ℝ) ≤ 4)).trans (by exact_mod_cast hMN)

theorem vertical_log_identity {N : ℕ} {ρ h : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (hh : 0 < h) :
    Real.log (ρ * N / (4 * h)) = Real.log N - Real.log (4 * h / ρ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_div (mul_pos hρ hn).ne' (mul_pos (by norm_num) hh).ne',
    Real.log_mul hρ.ne' hn.ne',
    Real.log_div (mul_pos (by norm_num) hh).ne' hρ.ne']
  ring

theorem vertical_lower (N : ℕ) (hN : 2 ≤ N) {ρ h θ : ℝ} (hρ : 0 < ρ) (hh : 0 < h)
    (hshift : 4 * h / ρ ≤ (N : ℝ) ^ θ) : 1 - θ ≤ vertical N ρ h := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl := Real.log_le_log (div_pos (mul_pos (by norm_num) hh) hρ) hshift
  rw [Real.log_rpow hn] at hl
  unfold vertical
  rw [vertical_log_identity (by omega) hρ hh]
  apply (le_div_iff₀ ht).mpr
  nlinarith only [hl]

theorem vertical_upper (N : ℕ) (hN : 2 ≤ N) {ρ h : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hh : 1 ≤ h) : vertical N ρ h ≤ 1 := by
  have ht : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hhpos : 0 < h := by linarith only [hh]
  have harg : 1 ≤ 4 * h / ρ := (le_div_iff₀ hρ).mpr (by nlinarith only [hh, hρ₁])
  unfold vertical
  rw [vertical_log_identity (by omega) hρ hhpos]
  apply (div_le_one ht).mpr
  linarith only [Real.log_nonneg harg]

theorem vertical_polylog_uniform (ρ K A θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℝ, h ≤ K * (Real.log N) ^ A → 4 * h / ρ ≤ (N : ℝ) ^ θ := by
  obtain ⟨N₀, h⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (4 * K / ρ) A θ hθ
  refine ⟨N₀, ?_⟩
  intro N hN shift hshift
  have hs := mul_le_mul_of_nonneg_left hshift (div_pos (by norm_num : (0 : ℝ) < 4) hρ).le
  have hbound : 4 * shift / ρ ≤ (4 * K / ρ) * (Real.log N) ^ A := by
    convert hs using 1 <;> ring
  exact hbound.trans (h N hN)

theorem horizontal_error_scale (N M : ℕ) (hN : 2 ≤ N) (hM : 0 < M) :
    Real.exp (-(horizontal N M * Real.log N)) = 4 / M := by
  have ht : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  rw [horizontal, div_mul_cancel₀ _ ht, Real.exp_neg, Real.exp_log (div_pos hm (by norm_num))]
  field_simp

theorem vertical_error_scale (N : ℕ) (hN : 2 ≤ N) {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) :
    Real.exp (-(vertical N ρ h * Real.log N)) = 4 * h / (ρ * N) := by
  have ht : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [vertical, div_mul_cancel₀ _ ht, Real.exp_neg,
    Real.exp_log (div_pos (mul_pos hρ hn) (mul_pos (by norm_num) hh))]
  field_simp

end PaperP1.DeterminantNormalizedWeights
