module

public import PaperP1.Analysis.FinalPrimeBandGeometry
public import PaperP1.Analysis.GrowingFirstGoodRegion
public import PaperP1.Analysis.NarrowBandReciprocalMass
public import PaperP1.Analysis.CeilingAmplificationOrder

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalPrimeOrderGeometry
open Finset Filter PaperP1
open scoped Classical

theorem eventual_geometry : ∀ᶠ N : ℕ in atTop,
    1 ≤ N ∧ 2 ≤ SlowPrimeBandSieve.lower N ∧ 4 ≤ GrowingFirstGoodRegion.width N ∧
    ∀ B j : ℕ, j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) →
      let u := NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j
      let k := CeilingAmplificationOrder.order N u
      (GrowingFirstGoodRegion.width N : ℝ) ≤ u ∧ 1 < u ∧
      SlowPrimeBandSieve.upper N/(2*SlowPrimeBandSieve.lower N) ≤ Real.log u ∧
      k ≤ GrowingFirstGoodRegion.width N ∧ (k : ℝ) ≤ 2*SlowPrimeBandSieve.lower N+1 ∧
      (N : ℝ) ≤ ((⌈u⌉₊^k : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2),
    GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop 4),
    GrowingFirstGoodRegion.width_geometry,PowerLogPrimeBand.geometry_eventually 5 (by norm_num)] with N hN hx hH hw hp
  refine ⟨hN,hx,hH,?_⟩
  intro B j hj
  dsimp only
  let x := SlowPrimeBandSieve.lower N
  let z := SlowPrimeBandSieve.upper N
  let H := GrowingFirstGoodRegion.width N
  let u := NarrowPrimeBands.anchor H j
  have hx2 : 2 ≤ x := hx
  have hxp : 0 < x := by linarith only [hx2]
  have hz : x^5 ≤ z := hp.2
  have hpow : 2*x^4 ≤ x^5 := by
    have hh := mul_le_mul_of_nonneg_left hx2 (pow_nonneg hxp.le 4)
    nlinarith only [hh]
  have hratio : 2*x^3 ≤ z/x := by
    apply (le_div_iff₀ hxp).mpr
    nlinarith only [hpow,hz]
  have hx3 : 8 ≤ x^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx2 3
    norm_num at hh
    exact hh
  have hP : ∀ p ∈ FinalPrimeBandGeometry.primes B N, 1 ≤ p := fun p hp ↦ (mem_filter.mp hp).2.one_le
  have hlo : ∀ p ∈ FinalPrimeBandGeometry.primes B N, Real.exp (z/x) ≤ (p : ℝ) := by
    intro p hp
    exact ((Nat.floor_lt (Real.exp_pos _).le).mp (mem_Ioc.mp (mem_filter.mp hp).1).1).le
  have hlower := NarrowBandReciprocalMass.anchor_lower H (by omega) (FinalPrimeBandGeometry.primes B N)
    hP (Real.exp (z/x)) hlo j hj
  change Real.exp (z/x)/2 ≤ u at hlower
  have hExp := Real.add_one_le_exp (z/x)
  have hHcap : (H : ℝ) ≤ x^3 := hw.2.1
  have hHLow : x^2 ≤ (H : ℝ) := hw.2.2
  have hHu : (H : ℝ) ≤ u := by nlinarith only [hHcap,hratio,hExp,hlower]
  have hHR : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hu : 1 < u := by linarith only [hHu,hHR]
  have hLog := Real.log_le_log (show 0 < Real.exp (z/x)/2 by positivity) hlower
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0),Real.log_exp] at hLog
  have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hLogLow : z/(2*x) ≤ Real.log u := by
    have he : z/(2*x)=(z/x)/2 := by ring
    rw [he]
    nlinarith only [hLog,hTwo,hratio,hx3]
  have hLogPos : 0 < Real.log u := Real.log_pos hu
  have hFrac : z/Real.log u ≤ 2*x := by
    apply (div_le_iff₀ hLogPos).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2*x)).mp hLogLow
    linarith only [hh]
  have hOrder : CeilingAmplificationOrder.order N u ≤ ⌈2*x⌉₊ := Nat.ceil_le_ceil hFrac
  have hCeil : ⌈2*x⌉₊ ≤ H := Nat.ceil_le.mpr (by nlinarith only [hHLow,hx2,sq_nonneg (x-1)])
  have hOrderR : (CeilingAmplificationOrder.order N u : ℝ) ≤ 2*x+1 :=
    (by exact_mod_cast hOrder : (_ : ℝ) ≤ (⌈2*x⌉₊ : ℝ)).trans (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*x)).le
  exact ⟨hHu,hu,hLogLow,hOrder.trans hCeil,hOrderR,
    CeilingAmplificationOrder.rounded_power_lower N (by omega) u hu⟩
end PaperP1.FinalPrimeOrderGeometry
