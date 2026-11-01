module

public import PaperP1.Asymptotics.QuadraticTailScale
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Comparing the manuscript's rounded threshold with a fixed power of N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NearLinearThreshold

open Filter PaperP1.CriticalBandScale

def scale (N : ℕ) : ℝ := Real.sqrt (Real.log N * Real.log (Real.log N))

def support (N L : ℕ) : ℕ := ⌈(N : ℝ) / L⌉₊

def threshold (N L : ℕ) (c : ℝ) : ℕ := ⌈(support N L : ℝ) * Real.exp (-c * scale N)⌉₊

theorem scale_bound_eventually (c : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ Real.log N ∧ c * scale N ≤ Real.log N / 20 := by
  have hratio := (PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one).comp
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have hsmall := hratio.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (400 * c ^ 2)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hsmall.and (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1)))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hsmall, hH⟩ := hN₀ N hN
  have hHpos : 0 < Real.log N := by linarith
  have hh : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hH
  have hsmall' : Real.log (Real.log N) / Real.log N ≤ 1 / (400 * c ^ 2) := by
    simpa only [Function.comp_apply, Real.rpow_one] using hsmall.le
  have hsmall'' := (div_le_iff₀ hHpos).mp hsmall'
  have hbudget : 400 * c ^ 2 * Real.log (Real.log N) ≤ Real.log N := by
    have hden : 0 < 400 * c ^ 2 := by positivity
    rw [div_eq_mul_inv, one_mul, mul_comm] at hsmall''
    rw [← div_eq_mul_inv] at hsmall''
    have h := (le_div_iff₀ hden).mp hsmall''
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hbudget hHpos.le
  have hsquare : (c * scale N) ^ 2 ≤ (Real.log N / 20) ^ 2 := by
    unfold scale
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hHpos.le hh)]
    nlinarith
  refine ⟨hH, ?_⟩
  have hnonneg : 0 ≤ c * scale N := mul_nonneg hc.le (Real.sqrt_nonneg _)
  nlinarith

theorem window_bound_eventually (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (L : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
  obtain ⟨Nband, hband⟩ := critical_band_scale C
  have hsmall := ((PNT.tendsto_pow_log_div_pow_atTop (1 / 20) 1 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (inv_pos.mpr upperScale_pos))
  obtain ⟨Npow, hNpow⟩ := eventually_atTop.mp hsmall
  refine ⟨max 2 (max Nband Npow), ?_⟩
  intro N hN L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := (hband N (by omega) L hcrit).2
  have hsmall' : Real.log N / (N : ℝ) ^ (1 / 20 : ℝ) ≤ upperScale⁻¹ := by
    simpa only [Function.comp_apply, Real.rpow_one] using (hNpow N (by omega)).le
  have h := (div_le_iff₀ (Real.rpow_pos_of_pos hn _)).mp hsmall'
  have hmul := mul_le_mul_of_nonneg_left h upperScale_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ upperScale_pos.ne', one_mul] at hmul
  have hL : (L : ℝ) ≤ upperScale * Real.log N := by
    simp only [Nat.cast_add, Nat.cast_one] at hb
    linarith
  exact hL.trans hmul

theorem threshold_ge_power (C c : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      QuadraticTailScale.threshold N ≤ (threshold N L c : ℝ) := by
  obtain ⟨Nscale, hscale⟩ := scale_bound_eventually c hc
  obtain ⟨Nwindow, hwindow⟩ := window_bound_eventually C
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  refine ⟨max 3 (max Nscale (max Nwindow Nfinite)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := (hfinite N (by omega) L hband).2.1
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hb := hwindow N (by omega) L hband
  have hs := (hscale N (by omega)).2
  have hexp : Real.exp (c * scale N) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
    rw [Real.rpow_def_of_pos hn]
    apply Real.exp_le_exp.mpr
    linarith
  have hproduct := mul_le_mul hb hexp (Real.exp_pos _).le (Real.rpow_nonneg hn.le _)
  have hcost : (L : ℝ) * Real.exp (c * scale N) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    convert hproduct using 1
    rw [← Real.rpow_add hn]
    norm_num
  have hbase : QuadraticTailScale.threshold N * (L : ℝ) * Real.exp (c * scale N) ≤ N := by
    have h := mul_le_mul_of_nonneg_left hcost
      (Real.rpow_nonneg hn.le (9 / 10 : ℝ))
    calc
      _ = (N : ℝ) ^ (9 / 10 : ℝ) * ((L : ℝ) * Real.exp (c * scale N)) := by
        unfold QuadraticTailScale.threshold
        ring
      _ ≤ (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := h
      _ = N := by rw [← Real.rpow_add hn]; norm_num
  have hdivide : QuadraticTailScale.threshold N ≤ (N : ℝ) / L * Real.exp (-c * scale N) := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (c * scale N))).mp
    rw [mul_assoc, ← Real.exp_add]
    have he : -c * scale N + c * scale N = 0 := by ring
    rw [he, Real.exp_zero, mul_one]
    apply (le_div_iff₀ hLreal).mpr
    nlinarith [hbase]
  calc
    _ ≤ (N : ℝ) / L * Real.exp (-c * scale N) := hdivide
    _ ≤ (support N L : ℝ) * Real.exp (-c * scale N) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.exp_pos _).le
    _ ≤ (threshold N L c : ℝ) := Nat.le_ceil _

end PaperP1.NearLinearThreshold
