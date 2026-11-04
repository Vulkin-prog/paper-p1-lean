module

public import PaperP1.Analysis.DeterminantCenterScales

/-! # Fixed inflation converts actual center comparisons to one-sided logarithmic errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantEffectiveHeights

theorem first_height_bounds {D E s₀ : ℝ} (hE : 0 < E)
    (hlo : D / (4 * E) ≤ s₀) (hhi : s₀ ≤ 2 * D / E) :
    D * E ≤ (2 * E) ^ 2 * s₀ ∧ (2 * E) ^ 2 * s₀ ≤ 8 * (D * E) := by
  have h₁ := (div_le_iff₀ (by positivity : 0 < 4 * E)).mp hlo
  have h₂ := (le_div_iff₀ hE).mp hhi
  have h₃ := mul_le_mul_of_nonneg_right h₁ hE.le
  have h₄ := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ 4 * E by positivity)
  constructor <;> nlinarith only [h₃, h₄]

theorem inflated_pair_height {K U V t₀ : ℝ} (hK : 1 ≤ K) (hU : 0 < U) (hV : 0 < V)
    (hlo : V / (K * U) ≤ t₀) (hhi : t₀ ≤ K * V / U) :
    U * V ≤ (K * U) ^ 2 * t₀ ∧ (K * U) ^ 2 * t₀ ≤ K ^ 3 * (U * V) := by
  have hK₀ : 0 < K := by linarith only [hK]
  have h₁ := (div_le_iff₀ (mul_pos hK₀ hU)).mp hlo
  have h₂ := (le_div_iff₀ hU).mp hhi
  have h₃ := mul_le_mul_of_nonneg_right h₁ (mul_pos hK₀ hU).le
  have h₄ := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ K ^ 2 * U by positivity)
  have h₅ := mul_le_mul_of_nonneg_right hK (mul_pos hU hV).le
  constructor <;> nlinarith only [h₃, h₄, h₅]

theorem log_comparison {P X K : ℝ} (hP : 0 < P) (hK : 0 < K) (hlo : P ≤ X) (hhi : X ≤ K * P) :
    Real.log P ≤ Real.log X ∧ Real.log X ≤ Real.log P + Real.log K := by
  have hX : 0 < X := hP.trans_le hlo
  refine ⟨Real.log_le_log hP hlo, ?_⟩
  have hh := Real.log_le_log hX hhi
  rw [Real.log_mul hK.ne' hP.ne'] at hh
  linarith only [hh]

theorem normalized_log_comparison {P X K T : ℝ} (hP : 0 < P) (hK : 0 < K) (hT : 0 < T)
    (hlo : P ≤ X) (hhi : X ≤ K * P) :
    Real.log P / T ≤ Real.log X / T ∧
      Real.log X / T ≤ Real.log P / T + Real.log K / T := by
  have h := log_comparison hP hK hlo hhi
  exact ⟨div_le_div_of_nonneg_right h.1 hT.le,
    (div_le_div_of_nonneg_right h.2 hT.le).trans_eq (add_div _ _ _)⟩

end PaperP1.DeterminantEffectiveHeights
