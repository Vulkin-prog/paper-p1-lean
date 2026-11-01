module

public import PaperP1.Asymptotics.QuadraticTailScale

/-! # The literal two-thirds-logarithmic order and its matching effective scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveTailScale

open Filter

def orderScale (N : ℕ) : ℝ := (Real.log (Real.log N)) ^ (2 / 3 : ℝ)

def rootScale (N : ℕ) : ℝ := (Real.log (Real.log N)) ^ (1 / 3 : ℝ)

def scale (N : ℕ) : ℝ := Real.log N / orderScale N

def order (N : ℕ) : ℕ := ⌈orderScale N⌉₊

def base (K : ℝ) (N : ℕ) : ℝ := Real.sqrt N * Real.exp (K * scale N)

def threshold (K : ℝ) (N : ℕ) : ℕ := ⌈base K N⌉₊

theorem root_mul_orderScale {N : ℕ} (hh : 0 < Real.log (Real.log N)) :
    rootScale N * orderScale N = Real.log (Real.log N) := by
  unfold rootScale orderScale
  rw [← Real.rpow_add hh]
  norm_num

theorem root_sq {N : ℕ} (hh : 0 ≤ Real.log (Real.log N)) :
    (rootScale N) ^ 2 = orderScale N := by
  unfold rootScale orderScale
  rw [← Real.rpow_two, ← Real.rpow_mul hh]
  norm_num

theorem unit_scales {N : ℕ} (hh : 1 ≤ Real.log (Real.log N)) :
    1 ≤ rootScale N ∧ 1 ≤ orderScale N ∧ orderScale N ≤ Real.log (Real.log N) := by
  refine ⟨Real.one_le_rpow hh (by norm_num), Real.one_le_rpow hh (by norm_num), ?_⟩
  calc
    _ ≤ (Real.log (Real.log N)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hh (by norm_num)
    _ = _ := Real.rpow_one _

theorem order_bounds {N : ℕ} (hh : 1 ≤ Real.log (Real.log N)) :
    orderScale N ≤ (order N : ℝ) ∧ (order N : ℝ) ≤ 2 * orderScale N := by
  have hq := (unit_scales hh).2.1
  refine ⟨Nat.le_ceil _, ?_⟩
  have hceil := (Nat.ceil_lt_add_one (by linarith : 0 ≤ orderScale N)).le
  change (⌈orderScale N⌉₊ : ℝ) ≤ _
  linarith

theorem scale_bounds {N : ℕ} (hh : 1 ≤ Real.log (Real.log N))
    (hsq : (Real.log (Real.log N)) ^ 2 ≤ Real.log N) :
    1 ≤ scale N ∧ Real.log (Real.log N) ≤ scale N := by
  obtain ⟨_, hq, hqh⟩ := unit_scales hh
  have hhpos : 0 < Real.log (Real.log N) := by linarith
  have hprod : Real.log (Real.log N) * orderScale N ≤ Real.log N := by
    calc
      _ ≤ Real.log (Real.log N) * Real.log (Real.log N) := mul_le_mul_of_nonneg_left hqh hhpos.le
      _ ≤ _ := by nlinarith
  have hhscale : Real.log (Real.log N) ≤ scale N :=
    (le_div_iff₀ (by linarith : 0 < orderScale N)).mpr hprod
  exact ⟨hh.trans hhscale, hhscale⟩

theorem scale_mul_orderScale {N : ℕ} (hh : 1 ≤ Real.log (Real.log N)) :
    scale N * orderScale N = Real.log N := by
  unfold scale
  exact div_mul_cancel₀ _ (by have h := (unit_scales hh).2.1; linarith)

theorem base_eq_exp {N : ℕ} (hn : 0 < (N : ℝ)) (K : ℝ) :
    base K N = Real.exp (Real.log N / 2 + K * scale N) := by
  unfold base
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn, ← Real.exp_add]
  congr 1
  ring

theorem conditions_eventually :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      2 ≤ Real.log N ∧ 1 ≤ Real.log (Real.log N) ∧
        (Real.log (Real.log N)) ^ 2 ≤ Real.log N ∧
          4 * Real.log N ≤ Real.sqrt N := by
  have hHlim := PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have hhlim := Real.tendsto_log_atTop.comp hHlim
  have hsquare := ((PNT.tendsto_pow_log_div_pow_atTop 1 2 zero_lt_one).comp hHlim).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hroot := ((PNT.tendsto_pow_log_div_pow_atTop (1 / 2) 1 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hHlim.eventually (eventually_ge_atTop 2)).and
    ((hhlim.eventually (eventually_ge_atTop 1)).and (hsquare.and hroot)))
  refine ⟨max N₀ 3, by omega, ?_⟩
  intro N hN
  obtain ⟨hH, hh, hsq, hroot⟩ := hN₀ N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsq' : (Real.log (Real.log N)) ^ 2 / Real.log N ≤ 1 := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.rpow_one] using hsq.le
  have hroot' : Real.log N / Real.sqrt N ≤ 1 / 4 := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.sqrt_eq_rpow] using hroot.le
  refine ⟨hH, hh, ?_, ?_⟩
  · have h := (div_le_iff₀ (by linarith : 0 < Real.log N)).mp hsq'
    simpa only [one_mul] using h
  · have h := (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mp hroot'
    linarith

theorem markov_order_bound {N : ℕ} (hH : 1 ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N)) (hroot : 4 * Real.log N ≤ Real.sqrt N)
    {K : ℝ} (hK : 0 ≤ K) : 2 * (order N : ℝ) ≤ base K N := by
  have hq := (unit_scales hh).2.2
  have hhH := Real.log_le_self (by linarith : 0 ≤ Real.log N)
  have hk := (order_bounds hh).2
  have hscale : 0 ≤ scale N := div_nonneg (by linarith) (by unfold orderScale; positivity)
  have he : 1 ≤ Real.exp (K * scale N) := Real.one_le_exp (mul_nonneg hK hscale)
  have hb : Real.sqrt N ≤ base K N := by
    unfold base
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (N : ℝ))
  linarith

end PaperP1.EffectiveTailScale
