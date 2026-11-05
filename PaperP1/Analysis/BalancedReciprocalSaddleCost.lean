module

public import PaperP1.Analysis.HardSaddleGrowth

/-! # Balanced reciprocal saddle costs and their fine error

A single actual saddle parameter can be used at every positive logarithmic
pivot cutoff. The finite cost loss is an explicit quadratic Ei remainder.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BalancedReciprocalSaddleCost

open Filter SaddleParameters SaddleScales SaddleAsymptotics SaddleBranch ExponentialIntegral HardSaddleGrowth

theorem finite_cost_lower (V E v : ℝ) (hV : 0 < V) (hE : 0 ≤ E) (hv : 0 < v) :
    2 * V - E ^ 2 / (4 * V) ≤ v + V * (V + E) / v - E := by
  let q := v + V * (V + E) / v - E
  by_cases hvV : v ≤ V
  · have hpos : 0 ≤ (v - V) ^ 2 + E * (V - v) := by positivity
    have hid : q * v - (2 * V) * v = (v - V) ^ 2 + E * (V - v) := by
      dsimp only [q]
      field_simp
      ring
    have htwo : 2 * V ≤ q := by
      apply (mul_le_mul_iff_left₀ hv).mp
      nlinarith only [hid, hpos]
    have herr : 0 ≤ E ^ 2 / (4 * V) := by positivity
    exact (by linarith only [herr] : 2 * V - E ^ 2 / (4 * V) ≤ 2 * V).trans htwo
  · have hVv : V ≤ v := by linarith only [hvV]
    have hid : q * (4 * v) - (8 * V * v - E ^ 2) = (2 * (v - V) - E) ^ 2 := by
      dsimp only [q]
      field_simp
      ring
    have hq : 2 * V - E ^ 2 / (4 * v) ≤ q := by
      apply (mul_le_mul_iff_left₀ (by positivity : 0 < 4 * v)).mp
      have he : (2 * V - E ^ 2 / (4 * v)) * (4 * v) = 8 * V * v - E ^ 2 := by field_simp; ring
      rw [he]
      nlinarith only [hid, sq_nonneg (2 * (v - V) - E)]
    have herr : E ^ 2 / (4 * v) ≤ E ^ 2 / (4 * V) :=
      div_le_div_of_nonneg_left (sq_nonneg E) (by positivity) (by nlinarith only [hVv])
    exact (sub_le_sub_left herr (2 * V)).trans hq

theorem balanced_identity (H : ℝ) (hH : saddleThreshold 1 ≤ H) :
    H * saddleParameter 1 H = saddleCutoff 1 H *
      (saddleCutoff 1 H + exponentialIntegral (saddleParameter 1 H)) := by
  have hs := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).2
  have hu : saddleParameter 1 H ≠ 0 := by
    have hh := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).1
    linarith only [hh, saddleParameterBase_ge_two]
  dsimp only [saddleHeight, saddleRatio, saddleCostParam] at hs
  rw [saddleCutoff]
  simp only [one_mul]
  dsimp only [saddleCostParam]
  field_simp [hu] at hs
  nlinarith only [hs]

theorem tendsto_ei_div_nu :
    Tendsto (fun H : ℝ ↦ exponentialIntegral (saddleParameter 1 H) / saddleNu 1 H)
      atTop (nhds 1) := by
  have ht := tendsto_normalizedExponentialIntegral.comp
    (tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ) < 1))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hu : saddleParameter 1 H ≠ 0 := by
    have hh := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).1
    linarith only [hh, saddleParameterBase_ge_two]
  rw [saddleNu, div_saddleCutoff_eq_ratio (by norm_num : (0 : ℝ) < 1) hH]
  dsimp only [Function.comp_apply, normalizedExponentialIntegral, saddleRatio]
  field_simp [hu, Real.exp_ne_zero _]

theorem tendsto_nu_div_cutoff :
    Tendsto (fun H : ℝ ↦ saddleNu 1 H / saddleCutoff 1 H) atTop (nhds 0) := by
  have huT := tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ) < 1)
  have hfactor := tendsto_saddleCostFactor.comp huT
  have ht : Tendsto (fun H : ℝ ↦ (saddleParameter 1 H)⁻¹ / saddleCostFactor (saddleParameter 1 H))
      atTop (nhds 0) := by
    have hh := huT.inv_tendsto_atTop.div hfactor (by norm_num : (1 : ℝ) ≠ 0)
    simp only [zero_div] at hh
    exact hh.congr' (Eventually.of_forall (fun _ ↦ rfl))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have huB := (saddleParameter_spec (by norm_num : (0 : ℝ) < 1) hH).1
  have hu : saddleParameter 1 H ≠ 0 := by linarith only [huB, saddleParameterBase_ge_two]
  have hf : saddleCostFactor (saddleParameter 1 H) ≠ 0 := (saddleCostFactor_pos huB).ne'
  rw [saddleNu, div_saddleCutoff_eq_ratio (by norm_num : (0 : ℝ) < 1) hH,
    saddleCutoff, one_mul, saddleCostParam_eq_exp_mul_factor]
  dsimp only [saddleRatio]
  field_simp [hu, hf, Real.exp_ne_zero _]

theorem tendsto_quadratic_error :
    Tendsto (fun H : ℝ ↦ exponentialIntegral (saddleParameter 1 H) ^ 2 /
      (saddleCutoff 1 H * saddleNu 1 H)) atTop (nhds 0) := by
  have ht := (tendsto_ei_div_nu.pow 2).mul tendsto_nu_div_cutoff
  have ht' : Tendsto (fun H : ℝ ↦ (exponentialIntegral (saddleParameter 1 H) / saddleNu 1 H) ^ 2 *
      (saddleNu 1 H / saddleCutoff 1 H)) atTop (nhds 0) := by
    simpa only [one_pow, mul_zero] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hH
  have hHp : 0 < H := (saddleThreshold_pos (by norm_num : (0 : ℝ) < 1)).trans_le hH
  have hν : 0 < saddleNu 1 H := div_pos hHp hV
  field_simp [hV.ne', hν.ne']

theorem uniform_cost_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ v : ℝ, 0 < v →
      2 * saddleCutoff 1 H - ε * saddleNu 1 H ≤
        v + H * saddleParameter 1 H / v - exponentialIntegral (saddleParameter 1 H) := by
  obtain ⟨H₀, hh⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (saddleThreshold 1)).and
      ((tendsto_ei_div_nu.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))).and
        (tendsto_quadratic_error.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 4 * ε)))))
  refine ⟨H₀, ?_⟩
  intro H hH v hv
  obtain ⟨hroot, hEi, herror⟩ := hh H hH
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  have hHp : 0 < H := (saddleThreshold_pos (by norm_num : (0 : ℝ) < 1)).trans_le hroot
  have hν : 0 < saddleNu 1 H := div_pos hHp hV
  have hE : 0 ≤ exponentialIntegral (saddleParameter 1 H) := by
    have hpos := (lt_div_iff₀ hν).mp hEi
    simpa only [zero_mul] using hpos.le
  have herr : exponentialIntegral (saddleParameter 1 H) ^ 2 / (4 * saddleCutoff 1 H) ≤ ε * saddleNu 1 H := by
    have hp := (div_le_iff₀ (mul_pos hV hν)).mp herror.le
    apply (div_le_iff₀ (by positivity : 0 < 4 * saddleCutoff 1 H)).mpr
    nlinarith only [hp]
  have hb := finite_cost_lower (saddleCutoff 1 H) (exponentialIntegral (saddleParameter 1 H)) v hV hE hv
  rw [← balanced_identity H hroot] at hb
  exact (sub_le_sub_left herr (2 * saddleCutoff 1 H)).trans hb

end PaperP1.BalancedReciprocalSaddleCost
