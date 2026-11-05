module

public import PaperP1.Analysis.HardSaddleGrowth
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Explicit density-iteration losses at the hard saddle

The finite ceiling and the prime-band constant cost a leading coefficient1/a
besides the reciprocal cutoff. This proves only a leading-scale estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothSaddleLoss

open Filter SaddleParameters SaddleScales HardSaddleGrowth

theorem finite_loss_upper (H V a b : ℝ) (hH : 0 < H) (hV : 0 < V)
    (ha : 0 < a) (hb : 0 < b) (hsq : H ≤ V ^ 2) (hr1 : b * V / (2 * H) ≤ 1) :
    V - (⌈H / (a * V)⌉₊ : ℝ) * Real.log (b * V / (2 * H)) ≤
      V + (H / (a * V) + 1) * (Real.log (2 / b) + Real.log H / 2) := by
  have hr : 0 < b * V / (2 * H) := by positivity
  have hlogr : Real.log (b * V / (2 * H)) ≤ 0 := Real.log_nonpos hr.le hr1
  have hlogV := Real.log_le_log hH hsq
  rw [Real.log_pow] at hlogV
  norm_num only [Nat.cast_ofNat] at hlogV
  have hlog : -Real.log (b * V / (2 * H)) ≤ Real.log (2 / b) + Real.log H / 2 := by
    rw [Real.log_div (mul_pos hb hV).ne' (mul_pos (by norm_num : (0 : ℝ) < 2) hH).ne',
      Real.log_mul hb.ne' hV.ne', Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hH.ne',
      Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hb.ne']
    linarith only [hlogV]
  have hk : (⌈H / (a * V)⌉₊ : ℝ) ≤ H / (a * V) + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ H / (a * V))).le
  calc
    _ = V + (⌈H / (a * V)⌉₊ : ℝ) * (-Real.log (b * V / (2 * H))) := by ring
    _ ≤ V + (H / (a * V) + 1) * (-Real.log (b * V / (2 * H))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hk (neg_nonneg.mpr hlogr))
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog (show 0 ≤ H / (a * V) + 1 by positivity))

theorem normalized_majorant_limit (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun H : ℝ ↦
      (saddleCutoff 1 H + (H / (a * saddleCutoff 1 H) + 1) *
        (Real.log (2 / b) + Real.log H / 2)) / saddleCutoff 1 H)
      atTop (nhds (1 + 1 / a)) := by
  have hInv : Tendsto (fun H : ℝ ↦ H * Real.log H / saddleCutoff 1 H ^ 2) atTop (nhds 2) := by
    have hh := (tendsto_saddleCutoff_square_normalized (by norm_num : (0 : ℝ) < 1)).inv₀
      (by norm_num : (1 : ℝ) / 2 ≠ 0)
    simpa only [inv_div, one_div, inv_inv] using hh
  have hHV : Tendsto (fun H : ℝ ↦ H / saddleCutoff 1 H ^ 2) atTop (nhds 0) := by
    apply (hInv.div_atTop Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
    have hlog : Real.log H ≠ 0 := (Real.log_pos hH).ne'
    field_simp [hlog]
  have hA := hInv.const_mul (1 / (2 * a))
  have hB := hHV.const_mul (Real.log (2 / b) / a)
  have hC := tendsto_cutoff_atTop.inv_tendsto_atTop.const_mul (Real.log (2 / b))
  have hD := tendsto_log_div_cutoff.const_mul (1 / 2 : ℝ)
  have hid : (1 / (2 * a)) * 2 = 1 / a := by ring
  have ht : Tendsto (fun H : ℝ ↦ 1 + (1 / (2 * a)) * (H * Real.log H / saddleCutoff 1 H ^ 2) +
      (Real.log (2 / b) / a) * (H / saddleCutoff 1 H ^ 2) +
      Real.log (2 / b) * (saddleCutoff 1 H)⁻¹ + (1 / 2) * (Real.log H / saddleCutoff 1 H))
      atTop (nhds (1 + 1 / a)) := by
    simpa only [hid, mul_zero, add_zero, Pi.inv_apply] using (((tendsto_const_nhds.add hA).add hB).add hC).add hD
  obtain ⟨HB, hbnd⟩ := square_band_eventually
  apply ht.congr'
  filter_upwards [eventually_ge_atTop HB] with H hH
  have hV := (hbnd H hH).2.1
  field_simp [hV.ne', ha.ne']
  ring

theorem eventual_loss_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 1 + 1 / a < c) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀,
      saddleCutoff 1 H - (⌈H / (a * saddleCutoff 1 H)⌉₊ : ℝ) *
        Real.log (b * saddleCutoff 1 H / (2 * H)) ≤ c * saddleCutoff 1 H := by
  obtain ⟨HB, hbnd⟩ := square_band_eventually
  have hsmall : Tendsto (fun H : ℝ ↦ (b / 2) * (saddleCutoff 1 H / H)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_cutoff_div_height.const_mul (b / 2)
  obtain ⟨H₀, hh⟩ := eventually_atTop.mp
    ((eventually_ge_atTop HB).and
      ((hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).and
        ((normalized_majorant_limit a b ha).eventually (eventually_lt_nhds hc))))
  refine ⟨H₀, ?_⟩
  intro H hH
  obtain ⟨hHB, hsmall, hlim⟩ := hh H hH
  obtain ⟨hHp, hVp, hsq, _⟩ := hbnd H hHB
  have hr1 : b * saddleCutoff 1 H / (2 * H) ≤ 1 := by
    convert hsmall.le using 1
    ring
  have hbound := (div_le_iff₀ hVp).mp hlim.le
  exact (finite_loss_upper H _ a b hHp hVp ha hb hsq hr1).trans hbound

end PaperP1.SmoothSaddleLoss
