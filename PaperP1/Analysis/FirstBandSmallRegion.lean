module

public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.SmallPrimeRegion

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FirstBandSmallRegion
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

def threshold (N : ℕ) : ℝ := 1/(SlowPrimeBandSieve.lower N)^10

def envelope (H N : ℕ) : ℝ :=
  (2*SupportedCoefficientSquareBudget.constant)*((H : ℝ)+1)^2/(SlowPrimeBandSieve.lower N)^18

theorem threshold_nonneg (N : ℕ) : 0 ≤ threshold N := by unfold threshold; positivity

theorem threshold_tendsto : Tendsto threshold atTop (nhds 0) := by
  change Tendsto (fun N ↦ 1/(SlowPrimeBandSieve.lower N)^10) atTop (nhds 0)
  have hh := (tendsto_inv_atTop_zero.comp SlowPrimeBandSieve.lower_tendsto).pow 10
  simpa only [threshold,Function.comp_def,one_div,inv_pow,zero_pow (by norm_num : 10 ≠ 0)] using hh

theorem envelope_tendsto (H : ℕ) : Tendsto (envelope H) atTop (nhds 0) := by
  change Tendsto (fun N ↦ (2*SupportedCoefficientSquareBudget.constant)*((H : ℝ)+1)^2/
    (SlowPrimeBandSieve.lower N)^18) atTop (nhds 0)
  have hh := ((tendsto_inv_atTop_zero.comp SlowPrimeBandSieve.lower_tendsto).pow 18).const_mul
    ((2*SupportedCoefficientSquareBudget.constant)*((H : ℝ)+1)^2)
  simpa only [envelope,Function.comp_def,div_eq_mul_inv,inv_pow,zero_pow (by norm_num : 18 ≠ 0),mul_zero] using hh

theorem first_prime_bounds (N : ℕ) (hU : 1 ≤ SlowPrimeBandSieve.upper N) :
    ∀ p ∈ TwoPrimeBandPopulation.first N, 1 ≤ p ∧ (p : ℝ) ≤ SlowPrimeBandSieve.upper N := by
  intro p hp
  obtain ⟨hpint,hpprime⟩ := mem_filter.mp hp
  refine ⟨hpprime.one_le,?_⟩
  have hh : (p : ℝ) ≤ (⌊SlowPrimeBandSieve.upper N⌋₊ : ℝ) := by
    exact_mod_cast (mem_Ioc.mp hpint).2
  exact hh.trans (Nat.floor_le (by linarith))

theorem indices_geometry (N H : ℕ) (hH : 0 < H)
    (hU : 1 ≤ SlowPrimeBandSieve.upper N) (hL : 1 ≤ SlowPrimeBandSieve.lower N) :
    (∀ j ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N),
      NarrowPrimeBands.anchor H j ≤ Real.log (N : ℝ)) ∧
    ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card : ℝ) ≤
      ((H : ℝ)+1)*SlowPrimeBandSieve.lower N := by
  have hP := first_prime_bounds N hU
  constructor
  · intro j hj
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    exact (NarrowPrimeBands.index_bounds H p hH (hP p hp).1).1.trans (hP p hp).2
  · have hc := NarrowPrimeBands.indices_card_bound H (TwoPrimeBandPopulation.first N)
      (SlowPrimeBandSieve.upper N) hP
    have hcR : ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card : ℝ) ≤
        (⌊(H : ℝ)*Real.log (SlowPrimeBandSieve.upper N)⌋₊ : ℝ)+1 := by exact_mod_cast hc
    have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg H : (0 : ℝ) ≤ H) (Real.log_nonneg hU))
    have hb : ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card : ℝ) ≤
        (H : ℝ)*SlowPrimeBandSieve.lower N+1 := by
      change _ ≤ (H : ℝ)*Real.log (SlowPrimeBandSieve.upper N)+1
      linarith only [hcR,hf]
    nlinarith only [hb,hL]

theorem quantitative_bound (N H : ℕ) (hN : 0 < N) (hH : 0 < H)
    (hU : 1 ≤ SlowPrimeBandSieve.upper N) (hL : 1 ≤ SlowPrimeBandSieve.lower N)
    (Q : Finset ℕ) (f : ℕ → ℂ) (hf : ∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) (hTN : T ≤ (N : ℝ)/Real.log (N : ℝ)) :
    (∫ t in SmallPrimeRegion.goodSet H (TwoPrimeBandPopulation.first N) f T (threshold N),
      ‖NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) Q f t‖^2) ≤ envelope H N := by
  obtain ⟨hanchor,hcard⟩ := indices_geometry N H hH hU hL
  have hlog : 0 < Real.log (N : ℝ) := by change 1 ≤ Real.log (N : ℝ) at hU; linarith
  have hb := SmallPrimeRegion.goodSet_bound N H hN (TwoPrimeBandPopulation.first N) Q f hf T
    (Real.log (N : ℝ)) (threshold N) hT hlog hTN (threshold_nonneg N) hanchor
  have hx : 0 < SlowPrimeBandSieve.lower N := by linarith
  have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg (NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card :
    (0 : ℝ) ≤ (NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card) hcard 2
  have hm := mul_le_mul_of_nonneg_right hcard2
    (mul_nonneg (sq_nonneg (threshold N))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) SupportedCoefficientSquareBudget.constant_pos.le))
  calc
    _ ≤ ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card : ℝ)^2*(threshold N)^2*
        (2*SupportedCoefficientSquareBudget.constant) := hb
    _ ≤ (((H : ℝ)+1)*SlowPrimeBandSieve.lower N)^2*(threshold N)^2*
        (2*SupportedCoefficientSquareBudget.constant) := by simpa only [mul_assoc] using hm
    _ = envelope H N := by
      unfold threshold envelope
      field_simp [hx.ne']

theorem small_uniform (H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : Finset ℕ, ∀ f : ℕ → ℂ,
      (∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in SmallPrimeRegion.goodSet H (TwoPrimeBandPopulation.first N) f T (threshold N),
        ‖NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) Q f t‖^2) ≤ ε := by
  obtain ⟨NE,hE⟩ := eventually_atTop.mp ((envelope_tendsto H).eventually (eventually_lt_nhds hε))
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨max 1 (max NE (max NU NL)),le_max_left _ _,?_⟩
  intro N hN Q f hf T hT hTN
  exact (quantitative_bound N H (by omega) hH (hU N (by omega)) (hL N (by omega)) Q f hf T hT hTN).trans
    (hE N (by omega)).le
end PaperP1.FirstBandSmallRegion
