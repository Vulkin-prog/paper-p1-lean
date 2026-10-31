module

public import PaperP1.Arithmetic.SharpPrimeCount

/-!
# The asymptotic logarithmic budget in the Griesmer inequality

PNT gives a sharp limit for `(pi(B)+1+t) log(64B) / B`, for each fixed t.
The additive coding rows and the constant inside the logarithm disappear in
this limit. All finite-prime counts retain the inclusive convention.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeLogBudget

open Filter Real LocalDefectBound LocalRigidityCode

theorem log_nat_tendsto_atTop : Tendsto (fun B : ℕ ↦ Real.log B) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem log_mul_div_log_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun B : ℕ ↦ Real.log (a * B) / Real.log B) atTop (nhds 1) := by
  have hinv := tendsto_inv_atTop_zero.comp log_nat_tendsto_atTop
  have hlim : Tendsto (fun B : ℕ ↦ Real.log a * (Real.log B)⁻¹ + 1)
      atTop (nhds (Real.log a * 0 + 1)) :=
    (tendsto_const_nhds.mul hinv).add tendsto_const_nhds
  have heq : (fun B : ℕ ↦ Real.log (a * B) / Real.log B)
      =ᶠ[atTop] (fun B : ℕ ↦ Real.log a * (Real.log B)⁻¹ + 1) := by
    filter_upwards [eventually_ge_atTop 2] with B hB
    have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    rw [Real.log_mul ha.ne' hb.ne', add_div, div_self hl.ne', div_eq_mul_inv]
  exact Tendsto.congr' heq.symm (by simpa only [mul_zero, zero_add] using hlim)

theorem log_nat_div_self_tendsto :
    Tendsto (fun B : ℕ ↦ Real.log B / (B : ℝ)) atTop (nhds 0) := by
  have h := (PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.rpow_one, Function.comp_def] using h

theorem log_mul_div_self_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun B : ℕ ↦ Real.log (a * B) / (B : ℝ)) atTop (nhds 0) := by
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun B : ℕ ↦ Real.log a * (B : ℝ)⁻¹ + Real.log B / B)
      atTop (nhds (Real.log a * 0 + 0)) :=
    (tendsto_const_nhds.mul hinv).add log_nat_div_self_tendsto
  have heq : (fun B : ℕ ↦ Real.log (a * B) / (B : ℝ))
      =ᶠ[atTop] (fun B : ℕ ↦ Real.log a * (B : ℝ)⁻¹ + Real.log B / B) := by
    filter_upwards [eventually_ge_atTop 1] with B hB
    have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    rw [Real.log_mul ha.ne' hb.ne', add_div, div_eq_mul_inv]
  exact Tendsto.congr' heq.symm (by simpa only [mul_zero, add_zero] using hlim)

/-- The exact finite Griesmer prime budget has sharp leading coefficient one. -/
theorem prime_log_budget_ratio_tendsto (t : ℕ) :
    Tendsto (fun B : ℕ ↦ ((primeCount B : ℝ) + 1 + t) *
      Real.log (64 * (B : ℝ)) / B) atTop (nhds 1) := by
  have hpc : Tendsto (fun B : ℕ ↦ (primeCount B : ℝ) * Real.log B / B)
      atTop (nhds 1) := by
    simpa only [primeCount_eq_primeCounting] using
      SharpPrimeCount.prime_counting_ratio_tendsto
  have hl := log_mul_div_log_tendsto 64 (by norm_num)
  have hs := log_mul_div_self_tendsto 64 (by norm_num)
  have hlim : Tendsto (fun B : ℕ ↦
      ((primeCount B : ℝ) * Real.log B / B) *
        (Real.log (64 * (B : ℝ)) / Real.log B) +
        (1 + (t : ℝ)) * (Real.log (64 * (B : ℝ)) / B))
      atTop (nhds (1 * 1 + (1 + (t : ℝ)) * 0)) :=
    (hpc.mul hl).add (tendsto_const_nhds.mul hs)
  have heq : (fun B : ℕ ↦ ((primeCount B : ℝ) + 1 + t) *
      Real.log (64 * (B : ℝ)) / B) =ᶠ[atTop] (fun B : ℕ ↦
      ((primeCount B : ℝ) * Real.log B / B) *
        (Real.log (64 * (B : ℝ)) / Real.log B) +
        (1 + (t : ℝ)) * (Real.log (64 * (B : ℝ)) / B)) := by
    filter_upwards [eventually_ge_atTop 2] with B hB
    have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    field_simp [hb.ne', hl.ne']
    ring
  exact Tendsto.congr' heq.symm (by simpa only [mul_one, mul_zero, add_zero] using hlim)

end PaperP1.PrimeLogBudget
