module

public import PaperP1.Analysis.FirstBandSmallRegion

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GrowingFirstGoodRegion
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

def width (N : ℕ) : ℕ := ⌊(SlowPrimeBandSieve.lower N)^3⌋₊

def envelope (N : ℕ) : ℝ := (8*SupportedCoefficientSquareBudget.constant)/(SlowPrimeBandSieve.lower N)^12

theorem width_tendsto : Tendsto width atTop atTop := by
  have hp := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp SlowPrimeBandSieve.lower_tendsto
  apply tendsto_atTop.2
  intro b
  filter_upwards [hp.eventually (eventually_ge_atTop (b : ℝ))] with N hN
  exact Nat.le_floor hN

theorem envelope_tendsto : Tendsto envelope atTop (nhds 0) := by
  change Tendsto (fun N ↦ (8*SupportedCoefficientSquareBudget.constant)/(SlowPrimeBandSieve.lower N)^12) atTop (nhds 0)
  have hh := ((tendsto_inv_atTop_zero.comp SlowPrimeBandSieve.lower_tendsto).pow 12).const_mul
    (8*SupportedCoefficientSquareBudget.constant)
  simpa only [Function.comp_def,div_eq_mul_inv,inv_pow,zero_pow (by norm_num : 12 ≠ 0),mul_zero] using hh

theorem width_geometry : ∀ᶠ N : ℕ in atTop,
    2 ≤ width N ∧ (width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 ∧
      (SlowPrimeBandSieve.lower N)^2 ≤ (width N : ℝ) := by
  filter_upwards [width_tendsto.eventually (eventually_ge_atTop 2),
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2)] with N hN hx
  have hfloor := Nat.lt_floor_add_one ((SlowPrimeBandSieve.lower N)^3)
  refine ⟨hN,Nat.floor_le (by positivity),?_⟩
  change _ ≤ (⌊(SlowPrimeBandSieve.lower N)^3⌋₊ : ℝ)
  have hsq : 0 ≤ (SlowPrimeBandSieve.lower N-2)*(SlowPrimeBandSieve.lower N)^2 := by positivity
  nlinarith only [hfloor,hsq,sq_nonneg (SlowPrimeBandSieve.lower N-1)]

theorem first_envelope_bound (N H : ℕ) (hx : 1 ≤ SlowPrimeBandSieve.lower N)
    (hH : (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3) : FirstBandSmallRegion.envelope H N ≤ envelope N := by
  have hxp : 0 < SlowPrimeBandSieve.lower N := by linarith
  have hx3 : 1 ≤ (SlowPrimeBandSieve.lower N)^3 := one_le_pow₀ hx
  have hbound : (H : ℝ)+1 ≤ 2*(SlowPrimeBandSieve.lower N)^3 := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ)+1) hbound 2
  have hsq' : ((H : ℝ)+1)^2 ≤ 4*(SlowPrimeBandSieve.lower N)^6 := by nlinarith only [hsq]
  unfold FirstBandSmallRegion.envelope envelope
  calc
    _ ≤ (2*SupportedCoefficientSquareBudget.constant)*(4*(SlowPrimeBandSieve.lower N)^6)/
        (SlowPrimeBandSieve.lower N)^18 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq' (mul_nonneg (by norm_num) SupportedCoefficientSquareBudget.constant_pos.le)) (by positivity)
    _ = _ := by field_simp [hxp.ne']; ring

theorem rectangle_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 →
      ∀ Q : Finset ℕ, ∀ f : ℕ → ℂ, (∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in SmallPrimeRegion.goodSet H (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N),
        ‖NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) Q f t‖^2) ≤ ε := by
  obtain ⟨NE,hE⟩ := eventually_atTop.mp (envelope_tendsto.eventually (eventually_lt_nhds hε))
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨max 1 (max NE (max NU NL)),le_max_left _ _,?_⟩
  intro N hN H hH hHcap Q f hf T hT hTN
  exact (FirstBandSmallRegion.quantitative_bound N H (by omega) (by omega) (hU N (by omega))
    (hL N (by omega)) Q f hf T hT hTN).trans
    ((first_envelope_bound N H (hL N (by omega)) hHcap).trans (hE N (by omega)).le)
end PaperP1.GrowingFirstGoodRegion
