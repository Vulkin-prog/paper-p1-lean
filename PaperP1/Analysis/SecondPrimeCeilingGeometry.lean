module

public import PaperP1.Analysis.ActualAnchorOrderGeometry
public import PaperP1.Analysis.CeilingAmplificationOrder

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SecondPrimeCeilingGeometry
open Finset Filter PaperP1
open scoped Classical

theorem eventual_geometry : ∀ᶠ N : ℕ in atTop,
    1 ≤ N ∧ 4 ≤ SlowPrimeBandSieve.lower N ∧ 4 ≤ GrowingFirstGoodRegion.width N ∧
    (SlowPrimeBandSieve.lower N)^5 ≤ SlowPrimeBandSieve.upper N ∧
    ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      let q := NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j
      let k := CeilingAmplificationOrder.order N q
      (GrowingFirstGoodRegion.width N : ℝ) ≤ q ∧ 1 < q ∧
      (SlowPrimeBandSieve.lower N)^2/2 ≤ Real.log q ∧ Real.log q ≤ (SlowPrimeBandSieve.lower N)^3 ∧
      1 ≤ k ∧ (k : ℝ) ≤ 3*SlowPrimeBandSieve.upper N/(SlowPrimeBandSieve.lower N)^2 ∧
      (k : ℝ) ≤ SlowPrimeBandSieve.upper N ∧
      (k : ℝ)*Real.log q ≤ SlowPrimeBandSieve.upper N+(SlowPrimeBandSieve.lower N)^3 ∧
      (N : ℝ) ≤ ((⌈q⌉₊^k : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 4),
    GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop 4),
    GrowingFirstGoodRegion.width_geometry,PowerLogPrimeBand.geometry_eventually 5 (by norm_num)] with N hN hx hH hw hp
  refine ⟨hN,hx,hH,hp.2,?_⟩
  intro j hj
  dsimp only
  let x := SlowPrimeBandSieve.lower N
  let z := SlowPrimeBandSieve.upper N
  let H := GrowingFirstGoodRegion.width N
  let q := NarrowPrimeBands.anchor H j
  have hx4 : 4 ≤ x := hx
  have hxp : 0 < x := by linarith only [hx4]
  have hz : x^5 ≤ z := hp.2
  have hx1 : 1 ≤ x := by linarith only [hx4]
  have hz2 : x^2 ≤ z := (pow_le_pow_right₀ hx1 (by norm_num : (2 : ℕ) ≤ 5)).trans hz
  have hzPos : 0 < z := (pow_pos hxp 2).trans_le hz2
  have hq := ActualAnchorOrderGeometry.second_anchor_bounds N H (by omega) (by linarith only [hx4]) j hj
  change Real.exp (x^2)/2 ≤ q ∧ 1 ≤ q ∧ Real.log q ≤ x^3 at hq
  have hpow : 4*x^3 ≤ x^4 := by
    have hh := mul_le_mul_of_nonneg_left hx4 (pow_nonneg hxp.le 3)
    nlinarith only [hh]
  have he := Real.quadratic_le_exp_of_nonneg (sq_nonneg x)
  have hHcap : (H : ℝ) ≤ x^3 := hw.2.1
  have hHq : (H : ℝ) ≤ q := by nlinarith only [hq.1,hpow,he,hHcap,sq_nonneg x]
  have hHR : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hq1 : 1 < q := by linarith only [hHq,hHR]
  have hlogPos : 0 < Real.log q := Real.log_pos hq1
  have hlog := Real.log_le_log (show 0 < Real.exp (x^2)/2 by positivity) hq.1
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0),Real.log_exp] at hlog
  have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hxSq : 16 ≤ x^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hx4 2
    norm_num at hh
    exact hh
  have hlogLow : x^2/2 ≤ Real.log q := by linarith only [hlog,hTwo,hxSq]
  have hRatio : z/Real.log q ≤ 2*z/x^2 := by
    have hh := div_le_div_of_nonneg_left hzPos.le (by positivity : 0 < x^2/2) hlogLow
    have heq : z/(x^2/2)=2*z/x^2 := by ring
    exact hh.trans_eq heq
  have hkCeil := (Nat.ceil_lt_add_one (div_nonneg hzPos.le hlogPos.le)).le
  change (CeilingAmplificationOrder.order N q : ℝ) ≤ z/Real.log q+1 at hkCeil
  have hOne : 1 ≤ z/x^2 := (le_div_iff₀ (pow_pos hxp 2)).mpr (by simpa only [one_mul] using hz2)
  have hkBound : (CeilingAmplificationOrder.order N q : ℝ) ≤ 3*z/x^2 := by
    have heq : 3*z/x^2=2*z/x^2+z/x^2 := by ring
    rw [heq]
    linarith only [hkCeil,hRatio,hOne]
  have hkZ : (CeilingAmplificationOrder.order N q : ℝ) ≤ z := by
    apply hkBound.trans
    apply (div_le_iff₀ (pow_pos hxp 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hxSq hzPos.le,hzPos]
  have hkPos : 1 ≤ CeilingAmplificationOrder.order N q := Nat.one_le_ceil_iff.mpr (div_pos hzPos hlogPos)
  have hkLog := CeilingAmplificationOrder.logarithmic_upper N q hq1
  change (_ : ℝ)*Real.log q ≤ z+Real.log q at hkLog
  exact ⟨hHq,hq1,hlogLow,hq.2.2,hkPos,hkBound,hkZ,
    hkLog.trans (add_le_add (le_refl z) hq.2.2),
    CeilingAmplificationOrder.rounded_power_lower N (by omega) q hq1⟩
end PaperP1.SecondPrimeCeilingGeometry
