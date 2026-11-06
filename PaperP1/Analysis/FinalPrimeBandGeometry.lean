module

public import PaperP1.Analysis.PowerLogPrimeBand
public import PaperP1.Analysis.FlexiblePrimeBandSieve

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalPrimeBandGeometry
open Finset Filter PaperP1
open scoped Classical

def lower (N : ℕ) : ℝ := Real.exp (SlowPrimeBandSieve.upper N/SlowPrimeBandSieve.lower N)

def upper (B N : ℕ) : ℝ := Real.exp (SlowPrimeBandSieve.upper N/(B : ℝ))

def primes (B N : ℕ) : Finset ℕ := FlexiblePrimeBandSieve.band lower (upper B) N

theorem exponent_lower_tendsto :
    Tendsto (fun N : ℕ ↦ SlowPrimeBandSieve.upper N/SlowPrimeBandSieve.lower N) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [PowerLogPrimeBand.geometry_eventually 2 (by norm_num),
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop (max 1 b))] with N hg hx
  have hx1 : 1 ≤ SlowPrimeBandSieve.lower N := (le_max_left 1 b).trans hx
  have hxp : 0 < SlowPrimeBandSieve.lower N := by linarith only [hx1]
  have hr : SlowPrimeBandSieve.lower N ≤ SlowPrimeBandSieve.upper N/SlowPrimeBandSieve.lower N := by
    apply (le_div_iff₀ hxp).mpr
    simpa only [PowerLogPrimeBand.lower,PowerLogPrimeBand.upper,pow_two] using hg.2
  exact ((le_max_right 1 b).trans hx).trans hr

theorem lower_tendsto : Tendsto lower atTop atTop := by
  change Tendsto (fun N : ℕ ↦ Real.exp (SlowPrimeBandSieve.upper N/SlowPrimeBandSieve.lower N)) atTop atTop
  exact Real.tendsto_exp_atTop.comp exponent_lower_tendsto

theorem upper_tendsto (B : ℕ) (hB : 0 < B) : Tendsto (upper B) atTop atTop := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  change Tendsto (fun N : ℕ ↦ Real.exp (SlowPrimeBandSieve.upper N/(B : ℝ))) atTop atTop
  exact Real.tendsto_exp_atTop.comp (Tendsto.atTop_div_const hBp SlowPrimeBandSieve.upper_tendsto)

theorem geometry_eventually (B : ℕ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ lower N ∧ lower N ≤ upper B N := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  filter_upwards [lower_tendsto.eventually (eventually_ge_atTop 2),
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop (max 1 (B : ℝ))),
    SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 0)] with N hl hx hz
  refine ⟨hl,?_⟩
  have hxB : (B : ℝ) ≤ SlowPrimeBandSieve.lower N := (le_max_right _ _).trans hx
  change Real.exp (SlowPrimeBandSieve.upper N/SlowPrimeBandSieve.lower N) ≤
    Real.exp (SlowPrimeBandSieve.upper N/(B : ℝ))
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hz hBp hxB)

theorem harmonic_gap_tendsto (B : ℕ) (hB : 0 < B) :
    Tendsto (fun N ↦ Real.log (Real.log (upper B N))-Real.log (Real.log (lower N))) atTop atTop := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have ht := Real.tendsto_log_atTop.comp SlowPrimeBandSieve.lower_tendsto
  have hs : Tendsto (fun N : ℕ ↦ Real.log (SlowPrimeBandSieve.lower N)-Real.log (B : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-Real.log (B : ℝ)) ht
  apply hs.congr'
  filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1),
    SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1)] with N hx hz
  have hxp : 0 < SlowPrimeBandSieve.lower N := by linarith only [hx]
  have hzp : 0 < SlowPrimeBandSieve.upper N := by linarith only [hz]
  dsimp only [lower,upper]
  rw [Real.log_exp,Real.log_exp,Real.log_div hzp.ne' hBp.ne',Real.log_div hzp.ne' hxp.ne']
  ring
end PaperP1.FinalPrimeBandGeometry
