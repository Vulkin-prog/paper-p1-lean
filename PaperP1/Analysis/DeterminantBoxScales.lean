module

public import PaperP1.Asymptotics.DeterminantSourceWeightMargin

/-! # Original source-box monomials bound every coordinate and both base logarithmic sizes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantBoxScales

theorem coordinate_bounds {c D U X : ℝ} (hc : 1 ≤ c) (hD : 1 ≤ D) (hU : 1 ≤ U)
    (hsource : c * D ^ 2 * U ≤ X) : D ^ 2 ≤ X ∧ D ≤ X ∧ U ≤ X := by
  have hc₀ : 0 ≤ c := by linarith only [hc]
  have hD₀ : 0 ≤ D := by linarith only [hD]
  have hU₀ : 0 ≤ U := by linarith only [hU]
  have hDsq : 1 ≤ D ^ 2 := by nlinarith only [hD]
  have hcU : 1 ≤ c * U := by nlinarith only [hc, hU, mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hU)]
  have h₁ := mul_le_mul_of_nonneg_right hcU (sq_nonneg D)
  have hcD : 1 ≤ c * D ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hDsq hc₀
    nlinarith only [hh, hc]
  have h₂ := mul_le_mul_of_nonneg_right hcD hU₀
  refine ⟨by nlinarith only [h₁, hsource], ?_, by nlinarith only [h₂, hsource]⟩
  have hd : D ≤ D ^ 2 := by nlinarith only [hD]
  nlinarith only [hd, h₁, hsource]

theorem log_DE_upper {N C c₁ c₂ D E U V : ℝ} (hN : 0 < N) (hC : 0 < C)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hD : 1 ≤ D) (hE : 1 ≤ E) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hfirst : c₁ * D ^ 2 * U ≤ C * N) (hsecond : c₂ * E ^ 2 * V ≤ C * N) :
    Real.log (D * E) ≤ Real.log N + Real.log C := by
  have hDpos : 0 < D := by linarith only [hD]
  have hEpos : 0 < E := by linarith only [hE]
  have hd := Real.log_le_log (sq_pos_of_pos hDpos) (coordinate_bounds hc₁ hD hU hfirst).1
  have he := Real.log_le_log (sq_pos_of_pos hEpos) (coordinate_bounds hc₂ hE hV hsecond).1
  rw [Real.log_pow, Real.log_mul hC.ne' hN.ne'] at hd he
  norm_num only [Nat.cast_ofNat] at hd he
  rw [Real.log_mul hDpos.ne' hEpos.ne']
  linarith only [hd, he]

theorem uniform_base_logs (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ c₁ c₂ D E U V : ℝ,
      1 ≤ c₁ → 1 ≤ c₂ → 1 ≤ D → 1 ≤ E → 1 ≤ U → 1 ≤ V →
      c₁ * D ^ 2 * U ≤ C * N → c₂ * E ^ 2 * V ≤ C * N →
      2 ≤ N ∧ Real.log (D * E) ≤ 3 * Real.log N ∧ Real.log (U * V) ≤ 3 * Real.log N := by
  obtain ⟨N₀, h⟩ := DeterminantNormalizedWeights.fixed_log_error C (1 / 2) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hfirst hsecond
  obtain ⟨hN₂, hlogC⟩ := h N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl : Real.log C ≤ (1 / 2 : ℝ) * Real.log N := (div_le_iff₀ ht).mp hlogC
  have hde := log_DE_upper hn hC hc₁ hc₂ hD hE hU hV hfirst hsecond
  have hcoeff : 1 ≤ c₁ * c₂ := by nlinarith only [hc₁, hc₂, mul_nonneg (sub_nonneg.mpr hc₁) (sub_nonneg.mpr hc₂)]
  have hDE : 1 ≤ D * E := by nlinarith only [hD, hE, mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hE)]
  have huv := DeterminantLogScale.log_parameter_upper hn hC
    (by linarith only [hc₁]) (by linarith only [hc₂]) (by linarith only [hD])
    (by linarith only [hE]) (by linarith only [hU]) (by linarith only [hV]) hcoeff hfirst hsecond
  exact ⟨hN₂, by linarith only [hde, hl, ht], by linarith only [huv, hl, Real.log_nonneg hDE]⟩

end PaperP1.DeterminantBoxScales
