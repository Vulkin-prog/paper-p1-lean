module

public import PaperP1.Analysis.ExpLogPrimeBand
public import PaperP1.Analysis.FlexiblePrimeBandSieve
public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.FinalPrimeBandGeometry

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalPrimeBandSieve
open Finset Filter PaperP1
open scoped Classical

theorem upper_rpow (B N : ℕ) (hN : 0 < N) :
    FinalPrimeBandGeometry.upper B N=(N : ℝ)^(1/(B : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hNp]
  unfold FinalPrimeBandGeometry.upper SlowPrimeBandSieve.upper
  congr 1
  ring

theorem upper_square_identity (B N : ℕ) (hN : 0 < N) :
    (FinalPrimeBandGeometry.upper B N)^2/(N : ℝ)=1/(N : ℝ)^(1-2/(B : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (Real.exp (Real.log (N : ℝ)/(B : ℝ)))^2/(N : ℝ)=
      Real.exp (2*(Real.log (N : ℝ)/(B : ℝ))-Real.log (N : ℝ)) := by
    rw [Real.exp_sub,show Real.exp (2*(Real.log (N : ℝ)/(B : ℝ)))=(Real.exp (Real.log (N : ℝ)/(B : ℝ)))^2 from Real.exp_nat_mul _ 2,Real.exp_log hNp]
  unfold FinalPrimeBandGeometry.upper SlowPrimeBandSieve.upper
  rw [he,Real.rpow_def_of_pos hNp,one_div,← Real.exp_neg]
  congr 1
  ring

theorem upper_square_tendsto (B : ℕ) (hB : 32 ≤ B) :
    Tendsto (fun N : ℕ ↦ (FinalPrimeBandGeometry.upper B N)^2/(N : ℝ)) atTop (nhds 0) := by
  have hBR : (32 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith only [hBR]
  have hr : 2/(B : ℝ) ≤ 1/16 := (div_le_iff₀ hBp).mpr (by linarith only [hBR])
  have hc : 0 < (1 : ℝ)-2/(B : ℝ) := by linarith only [hr]
  have hh := (PNT.tendsto_pow_log_div_pow_atTop (1-2/(B : ℝ)) 0 hc).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  dsimp only [Function.comp_def]
  rw [Real.rpow_zero]
  exact (upper_square_identity B N (by omega)).symm

theorem reciprocal_mass_tendsto (B : ℕ) (hB : 32 ≤ B) :
    Tendsto (fun N ↦ PrimeAvoidanceSieve.reciprocalMass (FinalPrimeBandGeometry.primes B N)) atTop atTop :=
  FlexiblePrimeBandSieve.reciprocal_mass_tendsto FinalPrimeBandGeometry.lower (FinalPrimeBandGeometry.upper B)
    FinalPrimeBandGeometry.lower_tendsto (FinalPrimeBandGeometry.geometry_eventually B (by omega))
    (FinalPrimeBandGeometry.harmonic_gap_tendsto B (by omega))

theorem missing_good_density_tendsto (B : ℕ) (hB : 32 ≤ B) :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ FlexiblePrimeBandSieve.good FinalPrimeBandGeometry.lower
      (FinalPrimeBandGeometry.upper B) N).card : ℝ)/(N : ℝ)) atTop (nhds 0) :=
  FlexiblePrimeBandSieve.missing_good_density_tendsto FinalPrimeBandGeometry.lower (FinalPrimeBandGeometry.upper B)
    FinalPrimeBandGeometry.lower_tendsto (FinalPrimeBandGeometry.geometry_eventually B (by omega))
    (FinalPrimeBandGeometry.harmonic_gap_tendsto B (by omega)) (upper_square_tendsto B hB)

theorem second_separation_eventually :
    ∀ᶠ N : ℕ in atTop, ExpLogPrimeBand.upper N < FinalPrimeBandGeometry.lower N := by
  filter_upwards [PowerLogPrimeBand.geometry_eventually 5 (by norm_num),
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2)] with N hg hx
  let x := SlowPrimeBandSieve.lower N
  have hx2 : 2 ≤ x := hx
  have hxp : 0 < x := by linarith only [hx2]
  have hpow : 2*x^4 ≤ x^5 := by
    have hh := mul_le_mul_of_nonneg_left hx2 (pow_nonneg hxp.le 4)
    nlinarith only [hh]
  have hz : x^5 ≤ SlowPrimeBandSieve.upper N := hg.2
  have hsmall : x^4 < SlowPrimeBandSieve.upper N := by
    have hh : 0 < x^4 := by positivity
    nlinarith only [hh,hpow,hz]
  change Real.exp (x^3) < Real.exp (SlowPrimeBandSieve.upper N/x)
  apply Real.exp_lt_exp.mpr
  apply (lt_div_iff₀ hxp).mpr
  nlinarith only [hsmall]

theorem disjoint_second_eventually (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, Disjoint (TwoPrimeBandPopulation.second N) (FinalPrimeBandGeometry.primes B N) := by
  filter_upwards [second_separation_eventually] with N hsep
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpU : (p : ℝ) ≤ ExpLogPrimeBand.upper N := by
    have hh : (p : ℝ) ≤ (⌊ExpLogPrimeBand.upper N⌋₊ : ℝ) := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
    exact hh.trans (Nat.floor_le (Real.exp_pos _).le)
  have hqL : FinalPrimeBandGeometry.lower N < (p : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp (mem_Ioc.mp (mem_filter.mp hq).1).1
  linarith only [hpU,hqL,hsep]
end PaperP1.FinalPrimeBandSieve
