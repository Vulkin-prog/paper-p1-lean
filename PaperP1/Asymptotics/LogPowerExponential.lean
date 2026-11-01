module

public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Asymptotics.UniformReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Exponentials of sublinear powers of a logarithmic height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogPowerExponential

open Filter

theorem log_power_ratio_tendsto (q : ℝ) (hq : q < 1) :
    Tendsto (fun N : ℕ ↦ (Real.log N) ^ q / Real.log N) atTop (nhds 0) := by
  have hlim := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - q)).comp
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have heq : (fun N : ℕ ↦ (Real.log N) ^ q / Real.log N) =ᶠ[atTop]
      (fun N : ℕ ↦ (Real.log N) ^ (-(1 - q))) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hlog]
    congr 1
    ring
  exact Tendsto.congr' heq.symm hlim

theorem exponential_le_rpow (K D q : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hq1 : q < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, (B : ℝ) ≤ D * Real.log N →
      Real.exp (K * (B : ℝ) ^ q) ≤ (N : ℝ) ^ ε := by
  have hlim := (log_power_ratio_tendsto q hq1).const_mul (K * D ^ q)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (by simpa only [mul_zero] using hε)))
  refine ⟨max 2 N₀, ?_⟩
  intro N hN B hB
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall : (K * D ^ q) * ((Real.log N) ^ q / Real.log N) ≤ ε := (hN₀ N (by omega)).le
  have hbudget : K * D ^ q * (Real.log N) ^ q ≤ ε * Real.log N := by
    rw [← mul_div_assoc] at hsmall
    exact (div_le_iff₀ hlog).mp hsmall
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg B) hB hq
  rw [Real.mul_rpow hD hlog.le] at hpow
  calc
    _ ≤ Real.exp (ε * Real.log N) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left hpow hK).trans (by simpa only [mul_assoc] using hbudget)
    _ = _ := by rw [Real.rpow_def_of_pos hn]; congr 1; ring

theorem uniformSubpolynomial (K D q : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    PaperP1.UniformSubpolynomialOn (fun N B ↦ (B : ℝ) ≤ D * Real.log N)
      (fun _ B ↦ Real.exp (K * (B : ℝ) ^ q)) := by
  intro k hk
  obtain ⟨N₀, hN₀⟩ := exponential_le_rpow K D q hK hD hq hq1 (1 / (k : ℝ)) (by positivity)
  refine ⟨max 1 N₀, ?_⟩
  intro N hN B hB
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := pow_le_pow_left₀ (Real.exp_pos _).le (hN₀ N (by omega) B hB) k
  rw [abs_of_pos (Real.exp_pos _)]
  refine h.trans_eq ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [one_div_mul_cancel hkR, Real.rpow_one]

end PaperP1.LogPowerExponential
