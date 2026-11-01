module

public import PaperP1.Asymptotics.QuadraticOrderMoments
public import PaperP1.Model.CountTailBounds
public import PaperP1.PNT.LogGrowth

/-! # A literal quadratic-logarithmic Markov order and an elementary cubic-log tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTailScale

open Filter PaperP1.Model PaperP1.FactorialCountMoments

def threshold (N : ℕ) : ℝ := (N : ℝ) ^ (9 / 10 : ℝ)

def order (N : ℕ) : ℕ := ⌈128 * (Real.log N) ^ 2⌉₊

theorem order_bounds (N : ℕ) (hH : 1 ≤ Real.log N) :
    128 * (Real.log N) ^ 2 ≤ (order N : ℝ) ∧
      (order N : ℝ) ≤ 129 * (Real.log N) ^ 2 := by
  constructor
  · exact Nat.le_ceil _
  · have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 128 * (Real.log N) ^ 2)).le
    have hsq : 1 ≤ (Real.log N) ^ 2 := by nlinarith
    change (⌈128 * (Real.log N) ^ 2⌉₊ : ℝ) ≤ _
    linarith

theorem scales_eventually :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      1 ≤ Real.log N ∧ 2 * (order N : ℝ) ≤ threshold N ∧
        4 ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
  have hlog := PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1)
  have hsmall := ((PNT.tendsto_pow_log_div_pow_atTop (9 / 10) 2 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 258))
  have hpower := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 4)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlog.and (hsmall.and hpower))
  refine ⟨max N₀ 3, by omega, ?_⟩
  intro N hN
  obtain ⟨hH, hsmall, hpower⟩ := hN₀ N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < threshold N := Real.rpow_pos_of_pos hn _
  have hsmall' : (Real.log N) ^ 2 / threshold N ≤ 1 / 258 := by
    norm_num only [Function.comp_apply, Real.rpow_two, threshold] at hsmall ⊢
    exact hsmall.le
  have hsq := (div_le_iff₀ hpow).mp hsmall'
  have hk := (order_bounds N hH).2
  refine ⟨hH, ?_, hpower⟩
  nlinarith

theorem ratio_bound {N : ℕ} (hn : 0 < (N : ℝ))
    (hfour : 4 ≤ (N : ℝ) ^ (1 / 20 : ℝ)) :
    2 * (2 * (N : ℝ) ^ (3 / 4 + 1 / 20 : ℝ)) / threshold N ≤
      (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hn _)).mpr
  calc
    _ = 4 * (N : ℝ) ^ (4 / 5 : ℝ) := by norm_num; ring
    _ ≤ (N : ℝ) ^ (1 / 20 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (-(1 / 20 : ℝ)) * threshold N := by
      unfold threshold
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
      norm_num

theorem power_bound {N : ℕ} (hn : 0 < (N : ℝ)) (hH : 1 ≤ Real.log N) :
    ((N : ℝ) ^ (-(1 / 20 : ℝ))) ^ order N ≤ Real.exp (-2 * (Real.log N) ^ 3) := by
  rw [Real.rpow_def_of_pos hn, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk := mul_le_mul_of_nonneg_right (order_bounds N hH).1 (by linarith : 0 ≤ Real.log N)
  nlinarith

theorem probability_bound (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.probability N L (threshold N) ≤ Real.exp (-2 * (Real.log N) ^ 3) := by
  obtain ⟨Nscale, hNscale, hscale⟩ := scales_eventually
  obtain ⟨Nmom, _, hmom⟩ := QuadraticOrderMoments.factorial_bound C 129 (1 / 20) (by norm_num) (by norm_num)
  refine ⟨max Nscale Nmom, by omega, ?_⟩
  intro N hN L hband
  obtain ⟨hH, hk, hfour⟩ := hscale N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmoment := hmom N (by omega) L hband (order N) (order_bounds N hH).2
  have hprob := CountTailBounds.probability_le_power N L (order N)
    (Real.rpow_pos_of_pos hn _) hk hmoment
  have hratio0 : 0 ≤ 2 * (2 * (N : ℝ) ^ (3 / 4 + 1 / 20 : ℝ)) / threshold N :=
    div_nonneg (by positivity) (Real.rpow_nonneg hn.le _)
  exact hprob.trans ((pow_le_pow_left₀ hratio0 (ratio_bound hn hfour) _).trans (power_bound hn hH))

end PaperP1.QuadraticTailScale
