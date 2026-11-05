module

public import PaperP1.Analysis.SmoothLowerBarrierGrowth
public import PaperP1.Analysis.BalancedReciprocalSaddleCost

/-! # The smooth lower-barrier cost at the actual hard saddle

The exact implicit root gives the fine cost gap and the small tilt.
No ordinary reciprocal-prime estimate is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothBarrierSaddleScale

open Filter SaddleParameters SaddleScales SaddleAsymptotics SaddleExpansion SaddleBranch
  ExponentialIntegral BalancedReciprocalSaddleCost SmoothLowerBarrierProfile SmoothLowerBarrierGrowth

theorem log_nu_identity (H : ℝ) (hH : saddleThreshold 1 ≤ H) :
    Real.log (saddleNu 1 H) = saddleParameter 1 H - Real.log (saddleParameter 1 H) := by
  have hu : 0 < saddleParameter 1 H := by
    have hh := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).1
    linarith only [hh, saddleParameterBase_ge_two]
  rw [saddleNu, div_saddleCutoff_eq_ratio (by norm_num : (0 : ℝ) < 1) hH,
    saddleRatio, Real.log_div (Real.exp_ne_zero _) hu.ne', Real.log_exp]

theorem cutoff_div_nu_identity (H : ℝ) (hH : saddleThreshold 1 ≤ H) :
    saddleCutoff 1 H / saddleNu 1 H = saddleParameter 1 H -
      normalizedExponentialIntegral (saddleParameter 1 H) := by
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hH
  calc
    _ = saddleCutoff 1 H ^ 2 / H := by rw [saddleNu]; field_simp
    _ = _ := by simpa only [one_mul] using saddleCutoff_square_div_identity (by norm_num : (0 : ℝ) < 1) hH

theorem tendsto_log_nu_div_parameter :
    Tendsto (fun H : ℝ ↦ Real.log (saddleNu 1 H) / saddleParameter 1 H) atTop (nhds 1) := by
  have huT := tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ) < 1)
  have hl : Tendsto (fun u : ℝ ↦ Real.log u / u) atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have ht : Tendsto (fun H : ℝ ↦ 1 - Real.log (saddleParameter 1 H) / saddleParameter 1 H)
      atTop (nhds 1) := by
    simpa only [Function.comp_def, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hl.comp huT)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hu : saddleParameter 1 H ≠ 0 := by
    have hh := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).1
    linarith only [hh, saddleParameterBase_ge_two]
  rw [log_nu_identity H hH]
  field_simp

theorem tendsto_loglog_nu_sub_log_parameter :
    Tendsto (fun H : ℝ ↦ Real.log (Real.log (saddleNu 1 H)) - Real.log (saddleParameter 1 H))
      atTop (nhds 0) := by
  have ht : Tendsto (fun H : ℝ ↦ Real.log (Real.log (saddleNu 1 H) / saddleParameter 1 H))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp tendsto_log_nu_div_parameter
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),
    (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).eventually
      (eventually_ge_atTop (2 : ℝ))] with H hH hν
  have hu : saddleParameter 1 H ≠ 0 := by
    have hh := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).1
    linarith only [hh, saddleParameterBase_ge_two]
  have hlog : Real.log (saddleNu 1 H) ≠ 0 := (Real.log_pos (by linarith only [hν])).ne'
  exact Real.log_div hlog hu

theorem tendsto_cost_gap (ε : ℝ) :
    Tendsto (fun H : ℝ ↦ (cost ε (saddleNu 1 H) - saddleCutoff 1 H) / saddleNu 1 H)
      atTop (nhds ε) := by
  have he := tendsto_normalizedExponentialIntegral.comp
    (tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ) < 1))
  have ht : Tendsto (fun H : ℝ ↦
      (Real.log (Real.log (saddleNu 1 H)) - Real.log (saddleParameter 1 H)) +
        (normalizedExponentialIntegral (saddleParameter 1 H) - 1) + ε) atTop (nhds ε) := by
    simpa only [Function.comp_def, sub_self, add_zero, zero_add] using
      (tendsto_loglog_nu_sub_log_parameter.add (he.sub_const 1)).add_const ε
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hH
  have hHp : 0 < H := (saddleThreshold_pos (by norm_num : (0 : ℝ) < 1)).trans_le hH
  have hν : saddleNu 1 H ≠ 0 := (div_pos hHp hV).ne'
  have hcost : cost ε (saddleNu 1 H) / saddleNu 1 H =
      Real.log (saddleNu 1 H) + Real.log (Real.log (saddleNu 1 H)) - 1 + ε := by
    rw [cost]
    field_simp
  rw [sub_div, hcost, cutoff_div_nu_identity H hH, log_nu_identity H hH]
  ring

theorem tendsto_tilt_div_cutoff (ε : ℝ) :
    Tendsto (fun H : ℝ ↦ tilt ε (saddleNu 1 H) / saddleCutoff 1 H) atTop (nhds 0) := by
  have hνT := tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)
  have hlog : Tendsto (fun u : ℝ ↦ Real.log u / u) atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have ht : Tendsto (fun H : ℝ ↦ (tilt ε (saddleNu 1 H) / Real.log (saddleNu 1 H)) *
      (Real.log (saddleNu 1 H) / saddleNu 1 H) * (saddleNu 1 H / saddleCutoff 1 H)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (((tendsto_tilt_div_log ε).comp hνT).mul (hlog.comp hνT)).mul tendsto_nu_div_cutoff
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),
    hνT.eventually (eventually_ge_atTop (2 : ℝ))] with H hH hν2
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hH
  have hν : saddleNu 1 H ≠ 0 := by linarith only [hν2]
  have hl : Real.log (saddleNu 1 H) ≠ 0 := (Real.log_pos (by linarith only [hν2])).ne'
  field_simp

theorem eventual_cost_upper (ε η : ℝ) (hεη : ε < η) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀,
      cost ε (saddleNu 1 H) ≤ saddleCutoff 1 H + η * saddleNu 1 H := by
  obtain ⟨H₀, h⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (saddleThreshold 1)).and
      ((tendsto_cost_gap ε).eventually (eventually_lt_nhds hεη)))
  refine ⟨H₀, ?_⟩
  intro H hH
  obtain ⟨hroot, he⟩ := h H hH
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  have hHp : 0 < H := (saddleThreshold_pos (by norm_num : (0 : ℝ) < 1)).trans_le hroot
  have hν : 0 < saddleNu 1 H := div_pos hHp hV
  have hh := (div_le_iff₀ hν).mp he.le
  linarith only [hh]

theorem eventual_tilt_upper (ε T : ℝ) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, saddleThreshold 1 ≤ H ∧ T ≤ saddleNu 1 H ∧
      tilt ε (saddleNu 1 H) ≤ saddleCutoff 1 H := by
  obtain ⟨H₀, h⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (saddleThreshold 1)).and
      (((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).eventually (eventually_ge_atTop T)).and
        ((tendsto_tilt_div_cutoff ε).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))))
  refine ⟨H₀, ?_⟩
  intro H hH
  obtain ⟨hroot, hT, he⟩ := h H hH
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  exact ⟨hroot, hT, by simpa only [one_mul] using (div_le_iff₀ hV).mp he.le⟩

end PaperP1.SmoothBarrierSaddleScale
