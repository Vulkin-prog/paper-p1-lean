module

public import PaperP1.Arithmetic.PrimeLogBudget
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.Order.Floor.Semifield

/-! # Inclusive prime counts at actual asymptotically linear integer cutoffs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledPrimeCounts

open Filter PaperP1.LocalDefectBound PaperP1.LocalRigidityCode

theorem cutoff_atTop {f : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hf : Tendsto (fun N : ℕ ↦ (f N : ℝ) / N) atTop (nhds a)) :
    Tendsto f atTop atTop := by
  have hprod := hf.pos_mul_atTop ha (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun N : ℕ ↦ (f N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ ↦ ((f N : ℝ) / N) * N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  exact tendsto_natCast_atTop_iff.mp (Tendsto.congr' heq.symm hprod)

theorem log_ratio {f : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hf : Tendsto (fun N : ℕ ↦ (f N : ℝ) / N) atTop (nhds a)) :
    Tendsto (fun N : ℕ ↦ Real.log (f N) / Real.log N) atTop (nhds 1) := by
  have hfTop := cutoff_atTop ha hf
  have hlog := hf.log ha.ne'
  have hrest := hlog.div_atTop PrimeLogBudget.log_nat_tendsto_atTop
  have heq : (fun N : ℕ ↦ Real.log (f N) / Real.log N) =ᶠ[atTop]
      (fun N : ℕ ↦ 1 + Real.log ((f N : ℝ) / N) / Real.log N) := by
    filter_upwards [eventually_ge_atTop 2, hfTop.eventually (eventually_ge_atTop 1)] with N hN hfN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hfn : (0 : ℝ) < f N := by exact_mod_cast (show 0 < f N by omega)
    have hlogN : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    rw [Real.log_div hfn.ne' hn.ne']
    field_simp
    ring
  exact Tendsto.congr' heq.symm (by simpa using tendsto_const_nhds.add hrest)

/-- The already proved PNT is transported through a literal integer cutoff. -/
theorem prime_count_scaled {f : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hf : Tendsto (fun N : ℕ ↦ (f N : ℝ) / N) atTop (nhds a)) :
    Tendsto (fun N : ℕ ↦ (primeCount (f N) : ℝ) * Real.log N / N) atTop (nhds a) := by
  have hfTop := cutoff_atTop ha hf
  have hPNT : Tendsto (fun N : ℕ ↦ (primeCount (f N) : ℝ) * Real.log (f N) / f N)
      atTop (nhds 1) := by
    simpa only [primeCount_eq_primeCounting, Function.comp_def] using
      SharpPrimeCount.prime_counting_ratio_tendsto.comp hfTop
  have hlogs : Tendsto (fun N : ℕ ↦ Real.log N / Real.log (f N)) atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using (log_ratio ha hf).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hlim := (hPNT.mul hf).mul hlogs
  have heq : (fun N : ℕ ↦ (primeCount (f N) : ℝ) * Real.log N / N) =ᶠ[atTop]
      (fun N : ℕ ↦ ((primeCount (f N) : ℝ) * Real.log (f N) / f N) *
        ((f N : ℝ) / N) * (Real.log N / Real.log (f N))) := by
    filter_upwards [eventually_ge_atTop 1, hfTop.eventually (eventually_ge_atTop 2)] with N hN hfN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hfn : (f N : ℝ) ≠ 0 := by exact_mod_cast (show f N ≠ 0 by omega)
    have hlogf : Real.log (f N) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < f N by omega))).ne'
    field_simp
  exact Tendsto.congr' heq.symm (by simpa only [one_mul, mul_one] using hlim)

theorem divided_cutoff_ratio (a b : ℕ) :
    Tendsto (fun N : ℕ ↦ ((a * N / b : ℕ) : ℝ) / N) atTop (nhds ((a : ℝ) / b)) := by
  have hcoef : 0 ≤ (a : ℝ) / b := by positivity
  have hlim := (tendsto_nat_floor_mul_div_atTop hcoef).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq (N : ℕ) : ⌊((a : ℝ) / b) * N⌋₊ = a * N / b := by
    rw [show ((a : ℝ) / b) * N = ((a * N : ℕ) : ℝ) / b by push_cast; ring,
      Nat.floor_div_eq_div]
  simpa only [Function.comp_def, heq] using hlim

theorem shifted_cutoff_ratio (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ ↦ ((a * N / b - d : ℕ) : ℝ) / N)
      atTop (nhds ((a : ℝ) / b)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlim := divided_cutoff_ratio a b
  have hTop := cutoff_atTop (div_pos haR hbR) hlim
  have hsmall : Tendsto (fun N : ℕ ↦ (d : ℝ) / N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun N : ℕ ↦ ((a * N / b - d : ℕ) : ℝ) / N) =ᶠ[atTop]
      (fun N : ℕ ↦ ((a * N / b : ℕ) : ℝ) / N - (d : ℝ) / N) := by
    filter_upwards [hTop.eventually (eventually_ge_atTop d)] with N hN
    rw [Nat.cast_sub hN, sub_div]
  exact Tendsto.congr' heq.symm (by simpa only [sub_zero] using hlim.sub hsmall)

theorem prime_count_divided_shifted (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ ↦ (primeCount (a * N / b - d) : ℝ) * Real.log N / N)
      atTop (nhds ((a : ℝ) / b)) := by
  apply prime_count_scaled (by exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb))
  exact shifted_cutoff_ratio a b d ha hb

end PaperP1.ScaledPrimeCounts
