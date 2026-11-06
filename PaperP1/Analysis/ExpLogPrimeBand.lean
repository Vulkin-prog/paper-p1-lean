module

public import PaperP1.Analysis.FlexiblePrimeBandSieve

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ExpLogPrimeBand
open Finset Filter PaperP1
open scoped Classical

def lower (N : ℕ) : ℝ := Real.exp ((SlowPrimeBandSieve.lower N)^2)
def upper (N : ℕ) : ℝ := Real.exp ((SlowPrimeBandSieve.lower N)^3)
def primes (N : ℕ) : Finset ℕ := FlexiblePrimeBandSieve.band lower upper N

theorem lower_tendsto : Tendsto lower atTop atTop := by
  exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp SlowPrimeBandSieve.lower_tendsto)

theorem geometry_eventually : ∀ᶠ N in atTop, 2 ≤ lower N ∧ lower N ≤ upper N := by
  filter_upwards [lower_tendsto.eventually (eventually_ge_atTop 2),
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1)] with N hl hs
  exact ⟨hl,Real.exp_le_exp.mpr (pow_le_pow_right₀ hs (by norm_num : (2 : ℕ) ≤ 3))⟩

theorem harmonic_gap_tendsto :
    Tendsto (fun N ↦ Real.log (Real.log (upper N))-Real.log (Real.log (lower N))) atTop atTop := by
  apply (Real.tendsto_log_atTop.comp SlowPrimeBandSieve.lower_tendsto).congr'
  apply Filter.Eventually.of_forall
  intro N
  dsimp only [Function.comp_def,lower,upper]
  rw [Real.log_exp,Real.log_exp,Real.log_pow,Real.log_pow]
  ring

theorem exp_power_square_small (k : ℕ) :
    Tendsto (fun N : ℕ ↦ (Real.exp ((SlowPrimeBandSieve.lower N)^k))^2/(N : ℝ)) atTop (nhds 0) := by
  have hr : Tendsto (fun N : ℕ ↦ (SlowPrimeBandSieve.lower N)^k/SlowPrimeBandSieve.upper N) atTop (nhds 0) := by
    simpa only [SlowPrimeBandSieve.lower,SlowPrimeBandSieve.upper,Function.comp_def,
      Real.rpow_natCast,Real.rpow_one] using
      (PNT.tendsto_pow_log_div_pow_atTop 1 (k : ℝ) zero_lt_one).comp SlowPrimeBandSieve.upper_tendsto
  have hneg : Tendsto (fun N : ℕ ↦ -(SlowPrimeBandSieve.upper N)/2) atTop atBot := by
    exact Filter.Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      (tendsto_neg_atTop_atBot.comp SlowPrimeBandSieve.upper_tendsto)
  have hb : Tendsto (fun N : ℕ ↦ Real.exp (-(SlowPrimeBandSieve.upper N)/2)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 2,
      hr.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4))] with N hN hs
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog : 0 < SlowPrimeBandSieve.upper N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hx := (div_lt_iff₀ hlog).mp hs
    have he : (Real.exp ((SlowPrimeBandSieve.lower N)^k))^2/(N : ℝ)=
        Real.exp (2*(SlowPrimeBandSieve.lower N)^k-SlowPrimeBandSieve.upper N) := by
      rw [Real.exp_sub,show Real.exp (SlowPrimeBandSieve.upper N)=(N : ℝ) from Real.exp_log hNp]
      congr 1
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [he]
    apply Real.exp_le_exp.mpr
    linarith

theorem upper_square_small : Tendsto (fun N : ℕ ↦ (upper N)^2/(N : ℝ)) atTop (nhds 0) :=
  exp_power_square_small 3

theorem reciprocal_mass_tendsto :
    Tendsto (fun N ↦ PrimeAvoidanceSieve.reciprocalMass (primes N)) atTop atTop :=
  FlexiblePrimeBandSieve.reciprocal_mass_tendsto lower upper lower_tendsto geometry_eventually harmonic_gap_tendsto

theorem excluded_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((FlexiblePrimeBandSieve.excluded lower upper N).card : ℝ)/(N : ℝ)) atTop (nhds 0) :=
  FlexiblePrimeBandSieve.excluded_density_tendsto lower upper lower_tendsto geometry_eventually harmonic_gap_tendsto upper_square_small

theorem missing_good_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ FlexiblePrimeBandSieve.good lower upper N).card : ℝ)/(N : ℝ)) atTop (nhds 0) :=
  FlexiblePrimeBandSieve.missing_good_density_tendsto lower upper lower_tendsto geometry_eventually harmonic_gap_tendsto upper_square_small
end PaperP1.ExpLogPrimeBand
