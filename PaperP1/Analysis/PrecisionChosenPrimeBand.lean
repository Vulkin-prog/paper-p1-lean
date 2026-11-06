module

public import PaperP1.Analysis.FlexiblePrimeBandSieve
public import PaperP1.Analysis.FixedPowerPrimeBand
public import PaperP1.Analysis.FixedPowerPrimeBandDensity

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrecisionChosenPrimeBand
open Finset Filter PaperP1 FixedPowerPrimeBand
open scoped Classical

theorem exponent_choice (b M : ℝ) (hb : 0 < b) (hM : 0 < M) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ M < Real.log (b/a) := by
  let a := b*Real.exp (-(M+1))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hExp : Real.exp (-(M+1)) < 1 := by
    have hh := Real.exp_lt_exp.mpr (show -(M+1)<(0 : ℝ) by linarith only [hM])
    simpa only [Real.exp_zero] using hh
  have hab : a < b := by
    have hh := mul_lt_mul_of_pos_left hExp hb
    simpa only [a,mul_one] using hh
  have hRatio : b/a=Real.exp (M+1) := by
    dsimp only [a]
    rw [Real.exp_neg]
    field_simp [hb.ne',(Real.exp_pos (M+1)).ne']
  refine ⟨a,ha,hab,?_⟩
  rw [hRatio,Real.log_exp]
  linarith

theorem small_missing_good (b ε : ℝ) (hb0 : 0 < b) (hb1 : b < 1/2) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ ∀ᶠ N : ℕ in atTop,
      ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (lower a) (lower b) N).card : ℝ)/(N : ℝ) ≤ ε := by
  let M : ℝ := 8/ε
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨a,ha,hab,hMass⟩ := exponent_choice b M hb0 hM
  refine ⟨a,ha,hab,?_⟩
  have hBound := FixedPowerPrimeBandDensity.missing_good_eventually_bound a b M (ε/2)
    ha hab.le hb1 hM hMass (by positivity)
  have he : 2/M=ε/4 := by dsimp only [M]; rw [div_div_eq_mul_div]; ring
  filter_upwards [hBound] with N hN
  rw [he] at hN
  linarith only [hN,hε]

theorem small_final_band (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1/32 ∧ ∀ᶠ N : ℕ in atTop,
      ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (lower a) (lower (1/32)) N).card : ℝ)/(N : ℝ) ≤ ε :=
  small_missing_good (1/32) ε (by norm_num) (by norm_num) hε
end PaperP1.PrecisionChosenPrimeBand
