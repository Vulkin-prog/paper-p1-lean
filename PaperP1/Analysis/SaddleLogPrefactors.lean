module

public import PaperP1.Analysis.SaddlePowerErrors

/-! # Every fixed logarithmic polynomial is negligible at the second saddle scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaddleLogPrefactors

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales

theorem logarithmic_power (K : ℝ) (hK : 0 < K) (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      K * (Real.log N) ^ d ≤ Real.exp (η * saddleNu 1 (Real.log N)) := by
  have ht : Tendsto (fun H : ℝ ↦ (Real.log K + (d : ℝ) * Real.log H) / saddleNu 1 H)
      atTop (nhds 0) := by
    have hc := (tendsto_const_nhds (x := Real.log K)).div_atTop
      (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1))
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hc.add
      ((tendsto_log_div_saddleNu (by norm_num : (0 : ℝ) < 1)).const_mul (d : ℝ))
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((hnlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) 1))).and
      ((ht.comp hnlog).eventually (eventually_lt_nhds hη)))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hdom, he⟩ := h N (by omega)
  have hH : 0 < Real.log N := by have := (le_max_right _ _).trans hdom; linarith
  have hV : 0 < saddleCutoff 1 (Real.log N) := saddleCutoff_pos (by norm_num) (by order)
  have hnu : 0 < saddleNu 1 (Real.log N) := div_pos hH hV
  change (Real.log K + (d : ℝ) * Real.log (Real.log N)) / saddleNu 1 (Real.log N) < η at he
  have hb := (div_le_iff₀ hnu).mp he.le
  calc
    _ = Real.exp (Real.log K + (d : ℝ) * Real.log (Real.log N)) := by
      rw [Real.exp_add, Real.exp_log hK, Real.exp_nat_mul, Real.exp_log hH]
    _ ≤ _ := Real.exp_le_exp.mpr hb

theorem logarithmic_width_le_height (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, D * Real.log N ≤ N := by
  have ht : Tendsto (fun N : ℕ ↦ D * (Real.log N / (N : ℝ))) atTop (nhds 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    simpa only [pow_one, one_mul, add_zero, mul_zero, Function.comp_def] using hh.const_mul D
  obtain ⟨N₀, h⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := h N (by omega)
  rw [← mul_div_assoc] at hh
  simpa only [one_mul] using (div_le_iff₀ hn).mp hh.le

end PaperP1.SaddleLogPrefactors
