module

public import PaperP1.Asymptotics.CriticalFreshBranchingBudget

/-! # Excluding old centres preserves the precise critical exceptional-set envelope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalFreshBranchingLog

open Filter PaperP1.CriticalBranchingBudget PaperP1.CriticalFreshBranchingBudget

theorem envelope_lower (K : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, (N : ℝ) ^ (1 / 2 : ℝ) ≤ exceptionEnvelope K N := by
  obtain ⟨NL, hl⟩ := eventually_atTop.mp (ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨max 3 NL, by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh : 1 ≤ Real.log (Real.log N) := hl N (by omega)
  have hhpos : 0 < Real.log (Real.log N) := by linarith only [hh]
  have hloghh := Real.log_le_self hhpos.le
  have hprod := mul_le_mul_of_nonneg_left hloghh hlog.le
  have hnegative : Real.log N * Real.log (Real.log (Real.log N)) /
      (9 * Real.log (Real.log N)) ≤ Real.log N / 9 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * Real.log (Real.log N))).mpr
    nlinarith only [hprod]
  have herror : 0 ≤ errorConstant K * (Real.log N / Real.log (Real.log N)) :=
    mul_nonneg (errorConstant_pos hK).le (by positivity)
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  unfold rate
  nlinarith only [hnegative, herror, hlog]

theorem fresh_le_twice (K : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, freshEnvelope K N ≤ 2 * exceptionEnvelope K N := by
  obtain ⟨NE, _hNE, he⟩ := envelope_lower K hK
  obtain ⟨NO, _hNO, ho⟩ := order_upper K (1 / 2) hK (by norm_num)
  refine ⟨max 3 (max NE NO), by omega, ?_⟩
  intro N hN
  have hmax : max 0 (orderCap K N) ≤ exceptionEnvelope K N :=
    max_le (Real.exp_pos _).le ((ho N (by omega)).trans (he N (by omega)))
  unfold freshEnvelope
  linarith only [hmax]

theorem fresh_log_upper (K : ℝ) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log (freshEnvelope K N) ≤ 2 / 3 * Real.log N -
        Real.log N * Real.log (Real.log (Real.log N)) / (9 * Real.log (Real.log N)) +
          c * (Real.log N / Real.log (Real.log N)) := by
  obtain ⟨NE, _hNE, he⟩ := fresh_le_twice K hK
  obtain ⟨NL, hl⟩ := eventually_atTop.mp (ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨errorConstant K + Real.log 2, add_pos_of_pos_of_nonneg (errorConstant_pos hK)
    (Real.log_nonneg (by norm_num)), max 3 (max NE NL), by omega, ?_⟩
  intro N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogbound := Real.log_le_log (freshEnvelope_pos K N) (he N (by omega))
  have heq : Real.log (2 * exceptionEnvelope K N) = Real.log 2 + rate K N := by
    rw [exceptionEnvelope, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  rw [heq] at hlogbound
  have hscale := (CubicLogTilt.log_scale_bounds hlog (hl N (by omega))).1
  have htwo := mul_le_mul_of_nonneg_left hscale (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  unfold rate at hlogbound
  nlinarith only [hlogbound, htwo]

end PaperP1.CriticalFreshBranchingLog
