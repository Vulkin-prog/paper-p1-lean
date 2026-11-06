module

public import PaperP1.Asymptotics.SlowPrimeBandSieve
public import PaperP1.Analysis.FlexiblePrimeBandSieve

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PowerLogPrimeBand
open Finset Filter PaperP1
open scoped Classical

def lower (A N : ℕ) : ℝ := (SlowPrimeBandSieve.lower N)^A
def upper (N : ℕ) : ℝ := SlowPrimeBandSieve.upper N
def primes (A N : ℕ) : Finset ℕ := FlexiblePrimeBandSieve.band (lower A) upper N

theorem lower_tendsto (A : ℕ) (hA : 0 < A) : Tendsto (lower A) atTop atTop := by
  exact (tendsto_pow_atTop (Nat.ne_of_gt hA)).comp SlowPrimeBandSieve.lower_tendsto

theorem geometry_eventually (A : ℕ) (hA : 0 < A) :
    ∀ᶠ N in atTop, 2 ≤ lower A N ∧ lower A N ≤ upper N := by
  have hr : Tendsto (fun N : ℕ ↦ lower A N/upper N) atTop (nhds 0) := by
    simpa only [lower,upper,SlowPrimeBandSieve.lower,SlowPrimeBandSieve.upper,
      Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (PNT.tendsto_pow_log_div_pow_atTop 1 (A : ℝ) zero_lt_one).comp SlowPrimeBandSieve.upper_tendsto
  filter_upwards [(lower_tendsto A hA).eventually (eventually_ge_atTop 2),
    SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1),
    hr.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with N hl hu hs
  refine ⟨hl,?_⟩
  exact ((div_lt_one (show 0 < upper N by change 1 ≤ upper N at hu; linarith)).mp hs).le

theorem harmonic_gap_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun N ↦ Real.log (Real.log (upper N))-Real.log (Real.log (lower A N))) atTop atTop := by
  have ht := SlowPrimeBandSieve.real_sub_log_tendsto.comp
    (Real.tendsto_log_atTop.comp SlowPrimeBandSieve.lower_tendsto)
  have hshift : Tendsto (fun N : ℕ ↦
      (Real.log (SlowPrimeBandSieve.lower N)-Real.log (Real.log (SlowPrimeBandSieve.lower N)))-Real.log (A : ℝ))
      atTop atTop := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-Real.log (A : ℝ)) ht
  apply hshift.congr'
  filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2)] with N hl
  change (Real.log (SlowPrimeBandSieve.lower N)-Real.log (Real.log (SlowPrimeBandSieve.lower N)))-Real.log (A : ℝ)=
    Real.log (SlowPrimeBandSieve.lower N)-Real.log (Real.log ((SlowPrimeBandSieve.lower N)^A))
  rw [Real.log_pow,Real.log_mul (by exact_mod_cast (Nat.ne_of_gt hA) : (A : ℝ) ≠ 0)
    (Real.log_pos (by linarith : 1 < SlowPrimeBandSieve.lower N)).ne']
  ring

theorem upper_square_small : Tendsto (fun N : ℕ ↦ (upper N)^2/(N : ℝ)) atTop (nhds 0) := by
  simpa only [upper,SlowPrimeBandSieve.upper,Real.rpow_one,Real.rpow_two,Function.comp_def] using
    (PNT.tendsto_pow_log_div_pow_atTop 1 2 zero_lt_one).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem reciprocal_mass_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun N ↦ PrimeAvoidanceSieve.reciprocalMass (primes A N)) atTop atTop :=
  FlexiblePrimeBandSieve.reciprocal_mass_tendsto (lower A) upper
    (lower_tendsto A hA) (geometry_eventually A hA) (harmonic_gap_tendsto A hA)

theorem excluded_density_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ ((FlexiblePrimeBandSieve.excluded (lower A) upper N).card : ℝ)/(N : ℝ))
      atTop (nhds 0) :=
  FlexiblePrimeBandSieve.excluded_density_tendsto (lower A) upper
    (lower_tendsto A hA) (geometry_eventually A hA) (harmonic_gap_tendsto A hA) upper_square_small

theorem missing_good_density_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (lower A) upper N).card : ℝ)/(N : ℝ))
      atTop (nhds 0) :=
  FlexiblePrimeBandSieve.missing_good_density_tendsto (lower A) upper
    (lower_tendsto A hA) (geometry_eventually A hA) (harmonic_gap_tendsto A hA) upper_square_small
end PaperP1.PowerLogPrimeBand
