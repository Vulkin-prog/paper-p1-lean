module

public import PaperP1.Analysis.HardSaddleGrowth
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # An actual integer product order at the coarse reciprocal saddle -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeProductSaddleChoice

open Filter SaddleParameters SaddleScales SaddleAsymptotics HardSaddleGrowth

theorem exists_order (Y₀ : ℕ) : ∃ H₀ : ℝ, ∀ H ≥ H₀,
    1 ≤ H ∧ ∃ k : ℕ, 1 ≤ k ∧
      Y₀ ≤ ⌊Real.exp (H / k)⌋₊ ∧ 8 * H ≤ Real.exp (H / k) ∧
      H / k + (k : ℝ) * Real.log (8 * H) ≤ 10 * saddleCutoff 1 H := by
  obtain ⟨HB, hb⟩ := square_band_eventually
  have ht := (tendsto_saddleCutoff_square_normalized (by norm_num : (0 : ℝ) < 1)).eventually
    (eventually_gt_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))
  have hv := tendsto_cutoff_div_height.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hl := tendsto_log_div_cutoff.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨H₁, h⟩ := eventually_atTop.mp (ht.and (hv.and hl))
  refine ⟨max HB (max H₁ (max 8 (Y₀ : ℝ))), ?_⟩
  intro H hH
  obtain ⟨hHpos, hVpos, _hHVsq, _hVsq⟩ := hb H ((le_max_left _ _).trans hH)
  obtain ⟨hquarter, hsmall, hlogsmall⟩ := h H ((le_max_left _ _).trans ((le_max_right _ _).trans hH))
  have hH8 : 8 ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hH))
  have hHY : (Y₀ : ℝ) ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hH))
  have hH1 : 1 ≤ H := by linarith only [hH8]
  have hlogpos : 0 < Real.log H := Real.log_pos (by linarith only [hH8])
  let V := saddleCutoff 1 H
  have hV : 0 < V := hVpos
  have hlogV : Real.log H ≤ V / 4 := by
    have hh := (div_le_iff₀ hV).mp hlogsmall.le
    change Real.log H ≤ (1 / 4 : ℝ) * V at hh
    linarith only [hh]
  have hVle : V ≤ H := by
    have hh := (div_le_iff₀ hHpos).mp hsmall.le
    exact hh.trans_eq (by ring)
  have hquarter' : H * Real.log H ≤ 4 * V ^ 2 := by
    have hh := (le_div_iff₀ (mul_pos hHpos hlogpos)).mp hquarter.le
    change (1 / 4 : ℝ) * (H * Real.log H) ≤ V ^ 2 at hh
    linarith only [hh]
  let ν := H / V
  let k := ⌈ν⌉₊
  have hν : 1 ≤ ν := (le_div_iff₀ hV).mpr (by simpa only [one_mul] using hVle)
  have hklo : ν ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ ν + 1 := (Nat.ceil_lt_add_one (by dsimp only [ν]; positivity)).le
  have hkpos : (0 : ℝ) < k := by linarith only [hklo, hν]
  have hk : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k from hν.trans hklo)
  have hdivhi : H / k ≤ V := by
    apply (div_le_iff₀ hkpos).mpr
    have hh := (div_le_iff₀ hV).mp hklo
    change H ≤ (k : ℝ) * V at hh
    nlinarith only [hh]
  have hdivlo : V / 2 ≤ H / k := by
    apply (le_div_iff₀ hkpos).mpr
    have hk2 : (k : ℝ) ≤ 2 * ν := by linarith only [hkhi, hν]
    have hk2' : (k : ℝ) ≤ (2 * H) / V := by simpa only [ν, mul_div_assoc] using hk2
    have hh := (le_div_iff₀ hV).mp hk2'
    change (k : ℝ) * V ≤ 2 * H at hh
    nlinarith only [hh]
  have hlog8 : Real.log (8 * H) ≤ 2 * Real.log H := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hH8
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hHpos.ne']
    linarith only [hh]
  have hscale : 8 * H ≤ Real.exp (H / k) := by
    calc
      _ = Real.exp (Real.log (8 * H)) := (Real.exp_log (by positivity : 0 < 8 * H)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hlog8, hlogV, hdivlo])
  have hfloor : Y₀ ≤ ⌊Real.exp (H / k)⌋₊ := by
    apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    have hh : H ≤ 8 * H := by linarith only [hHpos]
    exact hHY.trans (hh.trans hscale)
  have hmain : ν * (2 * Real.log H) ≤ 8 * V := by
    dsimp only [ν]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hV).mpr
    nlinarith only [hquarter']
  have hklog : (k : ℝ) * Real.log (8 * H) ≤ (ν + 1) * (2 * Real.log H) :=
    mul_le_mul hkhi hlog8 (Real.log_nonneg (by nlinarith only [hH8] : (1 : ℝ) ≤ 8 * H)) (by positivity)
  refine ⟨hH1, k, hk, hfloor, hscale, ?_⟩
  change H / k + (k : ℝ) * Real.log (8 * H) ≤ 10 * V
  nlinarith only [hdivhi, hklog, hmain, hlogV, hV]

end PaperP1.PrimeProductSaddleChoice
