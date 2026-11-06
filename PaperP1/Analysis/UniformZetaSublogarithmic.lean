module

public import PaperP1.Analysis.ActualZetaTail
public import PaperP1.Analysis.ZetaLogarithmicEnvelope

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformZetaSublogarithmic
open Finset Filter PaperP1
open scoped Classical

theorem uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ‖riemannZeta (ActualZetaTail.argument σ t)‖ ≤ ε*Real.log |t| := by
  let α : ℝ := min (ε/4) (1/4)
  have hα0 : 0 < α := by dsimp only [α]; exact lt_min (by positivity) (by norm_num)
  have hα1 : α ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hαε : α < ε := by
    have hh : α ≤ ε/4 := min_le_left _ _
    linarith only [hh,hε]
  obtain ⟨TB,hTB,hBound⟩ := ZetaLogarithmicEnvelope.uniform_bound α hα0 hα1
  have hLimit := ZetaLogarithmicEnvelope.envelope_normalized_tendsto α hα0
  obtain ⟨TL,hTL⟩ := eventually_atTop.mp ((tendsto_order.mp hLimit).2 ε hαε)
  refine ⟨max TB TL,hTB.trans (le_max_left _ _),?_⟩
  intro t ht σ hσ0 hσ1
  have htB : TB ≤ |t| := (le_max_left _ _).trans ht
  have htL : TL ≤ |t| := (le_max_right _ _).trans ht
  have ht8 : 8 ≤ |t| := hTB.trans htB
  have hLog : 0 < Real.log |t| := Real.log_pos (by linarith only [ht8])
  have hEnv := (div_lt_iff₀ hLog).mp (hTL |t| htL)
  exact (hBound t htB σ hσ0 hσ1).trans hEnv.le

theorem normalized_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ‖riemannZeta (ActualZetaTail.argument σ t)‖/Real.log |t| ≤ ε := by
  obtain ⟨T₀,hT₀,hBound⟩ := uniform_bound ε hε
  refine ⟨T₀,hT₀,?_⟩
  intro t ht σ hσ0 hσ1
  have ht8 : 8 ≤ |t| := hT₀.trans ht
  have hLog := Real.log_pos (show 1 < |t| by linarith only [ht8])
  exact (div_le_iff₀ hLog).mpr (hBound t ht σ hσ0 hσ1)

theorem polynomial_height_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      T₀ ≤ |t| → |t| ≤ (N : ℝ)^B → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ‖riemannZeta (ActualZetaTail.argument σ t)‖ ≤ ε*Real.log (N : ℝ) := by
  obtain ⟨T₀,hT₀,hBound⟩ := uniform_bound (ε/B) (by positivity)
  refine ⟨T₀,hT₀,?_⟩
  intro N hN t ht hUpper σ hσ0 hσ1
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht8 : 8 ≤ |t| := hT₀.trans ht
  have htP : 0 < |t| := by linarith only [ht8]
  have hLog := Real.log_le_log htP hUpper
  rw [Real.log_rpow hNP] at hLog
  calc
    _ ≤ (ε/B)*Real.log |t| := hBound t ht σ hσ0 hσ1
    _ ≤ (ε/B)*(B*Real.log (N : ℝ)) := mul_le_mul_of_nonneg_left hLog (by positivity)
    _ = _ := by field_simp
end PaperP1.UniformZetaSublogarithmic
