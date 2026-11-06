module

public import PaperP1.Analysis.ActualZetaTail
public import PaperP1.Analysis.PolynomialLogarithmicCancellation
public import PaperP1.Analysis.ZetaCutoffGeometry
public import PaperP1.Analysis.ZetaHeadAndTail
public import PaperP1.Analysis.ZetaMiddleEstimate

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ZetaLogarithmicEnvelope
open Finset Filter PaperP1 PolynomialLogarithmicCancellation DampedLogarithmicIntegral ZetaCutoffGeometry
open scoped Classical

def exponent (α : ℝ) : ℝ := α*decay (1/4) (1/α)

def middle (α y : ℝ) : ℝ :=
  ((Real.log 2+2*Real.log y)/Real.log 2+1)*constant (1/α)/y^(exponent α)

def envelope (α y : ℝ) : ℝ := 1+Real.log 2+α*Real.log y+middle α y+8/y

theorem exponent_pos (α : ℝ) (hα : 0 < α) : 0 < exponent α :=
  mul_pos hα (decay_pos (1/4) (1/α) (by norm_num))

theorem uniform_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ‖riemannZeta (ActualZetaTail.argument σ t)‖ ≤ envelope α |t| := by
  obtain ⟨T₀,hT₀,hMiddle⟩ := ZetaMiddleEstimate.uniform_bound α hα0 hα1
  refine ⟨T₀,hT₀,?_⟩
  intro t ht σ hσ0 hσ1
  have ht8 : 8 ≤ |t| := hT₀.trans ht
  have ht1 : 1 ≤ |t| := by linarith only [ht8]
  have hHead := ZetaHeadAndTail.rounded_head_bound α |t| hα0.le ht1 σ t hσ0.le
  have hMid : ‖∑ n ∈ Ico (lower α |t|) (upper |t|), integrand σ t n‖ ≤ middle α |t| :=
    hMiddle t ht σ hσ0.le
  have hTail := ZetaHeadAndTail.rounded_tail_bound σ t hσ0 hσ1 ht1
  have he : riemannZeta (ActualZetaTail.argument σ t)=
      ((∑ n ∈ range (lower α |t|), integrand σ t n)+
        (∑ n ∈ Ico (lower α |t|) (upper |t|), integrand σ t n))+
      (riemannZeta (ActualZetaTail.argument σ t)-(∑ n ∈ range (upper |t|), integrand σ t n)) := by
    rw [ZetaHeadAndTail.head_split (lower α |t|) (upper |t|) (ordered α |t| hα1 ht1) σ t]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hHead hMid)) hTail)

theorem middle_normalized_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun y : ℝ ↦ middle α y/Real.log y) atTop (nhds 0) := by
  have hLog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hPower := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (exponent_pos α hα))
  have hh := (((hLog.const_mul 2).add (tendsto_const_nhds (x := 2/Real.log 2))).mul hPower).const_mul (constant (1/α))
  have hLimit : Tendsto (fun y : ℝ ↦ constant (1/α)*((2/Real.log y+2/Real.log 2)/y^(exponent α))) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero,zero_add,add_zero,div_eq_mul_inv] using hh
  apply hLimit.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  have hLogY := (Real.log_pos hy).ne'
  have hLog2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hYP : 0 < y := by linarith only [hy]
  unfold middle
  field_simp [hLogY,hLog2,(Real.rpow_pos_of_pos hYP (exponent α)).ne']
  ring

theorem envelope_normalized_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun y : ℝ ↦ envelope α y/Real.log y) atTop (nhds α) := by
  have hLog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hConst := hLog.const_mul (1+Real.log 2)
  have hTail := ((tendsto_inv_atTop_zero.const_mul 8).mul hLog)
  have hTotal := ((hConst.add (tendsto_const_nhds (x := α))).add (middle_normalized_tendsto α hα)).add hTail
  have hLimit : Tendsto (fun y : ℝ ↦ (1+Real.log 2)/Real.log y+α+middle α y/Real.log y+(8/y)/Real.log y)
      atTop (nhds α) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero,zero_mul,zero_add,add_zero] using hTotal
  apply hLimit.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  have hLogY := (Real.log_pos hy).ne'
  unfold envelope
  field_simp [hLogY]
end PaperP1.ZetaLogarithmicEnvelope
