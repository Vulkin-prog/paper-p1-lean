module

public import PaperP1.Analysis.HardSaddleExplicitScale

/-! # Finite logarithmic variation of the explicit saddle

These estimates keep the small square-part parameter in the error bound.
The logarithmic difference bound avoids differentiating an asymptotic
remainder in the ordinary reciprocal-prime theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitSaddleVariation

open PaperP1.HardSaddleExplicitScale

theorem log_difference_bound {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    Real.log H - Real.log t ≤ (H - t) / t := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hH ht)
  rw [Real.log_div hH.ne' ht.ne'] at hh
  have heq : (H - t) / t = H / t - 1 := by field_simp
  rwa [heq]

theorem core_difference_bound {t H : ℝ} (ht : 0 < t) (htlog : 1 ≤ Real.log t) (htH : t ≤ H) :
    0 ≤ logCore H - logCore t ∧ logCore H - logCore t ≤ 2 * (H - t) / t := by
  have hH : 0 < H := ht.trans_le htH
  have hlog : Real.log t ≤ Real.log H := Real.log_le_log ht htH
  have hlogpos : 0 < Real.log t := by linarith
  have hlogHpos : 0 < Real.log H := hlogpos.trans_le hlog
  have hloglog : Real.log (Real.log t) ≤ Real.log (Real.log H) := Real.log_le_log hlogpos hlog
  have hd := log_difference_bound ht hH
  have hdd := (log_difference_bound hlogpos hlogHpos).trans (div_le_self (by linarith : 0 ≤ Real.log H - Real.log t) htlog)
  constructor
  · unfold logCore
    linarith only [hlog, hloglog]
  · calc
      logCore H - logCore t ≤ 2 * (Real.log H - Real.log t) := by
        unfold logCore
        linarith only [hdd]
      _ ≤ 2 * ((H - t) / t) := mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = _ := by ring

theorem scale_monotone {t H : ℝ} (ht : 0 ≤ t) (htH : t ≤ H)
    (htcore : 0 ≤ logCore t) (hcore : logCore t ≤ logCore H) : explicitScale t ≤ explicitScale H := by
  apply Real.sqrt_le_sqrt
  have hh := mul_le_mul htH hcore htcore (ht.trans htH)
  nlinarith only [hh]

theorem finite_scale_difference {t H : ℝ} (ht : 0 < t) (htlog : 1 ≤ Real.log t)
    (htH : t ≤ H) (htcore : 0 ≤ logCore t) (hHcore : 1 ≤ logCore H) :
    0 ≤ explicitScale H - explicitScale t ∧
    explicitScale H - explicitScale t ≤ 3 * (H - t) * explicitScale H / H := by
  have hH : 0 < H := ht.trans_le htH
  obtain ⟨hc0, hc⟩ := core_difference_bound ht htlog htH
  have hg := scale_monotone ht.le htH htcore (by linarith only [hc0])
  have hG : 0 < explicitScale H := by unfold explicitScale; positivity
  have hsqH : explicitScale H ^ 2 = 2 * H * logCore H := Real.sq_sqrt (by positivity)
  have hsqt : explicitScale t ^ 2 = 2 * t * logCore t := Real.sq_sqrt (by positivity)
  have hcm : t * (logCore H - logCore t) ≤ 2 * (H - t) := by
    have hh := (le_div_iff₀ ht).mp hc
    nlinarith only [hh]
  have hprod : (explicitScale H - explicitScale t) * explicitScale H ≤
      6 * (H - t) * logCore H := by
    have hn := mul_nonneg (sub_nonneg.mpr hg) (Real.sqrt_nonneg (2 * t * logCore t))
    have hq := mul_nonneg (sub_nonneg.mpr htH) (sub_nonneg.mpr hHcore)
    change 0 ≤ (explicitScale H - explicitScale t) * explicitScale t at hn
    nlinarith only [hsqH, hsqt, hcm, hn, hq]
  refine ⟨sub_nonneg.mpr hg, ?_⟩
  apply (mul_le_mul_iff_left₀ hG).mp
  calc
    _ ≤ 6 * (H - t) * logCore H := by nlinarith only [hprod]
    _ = explicitScale H * (3 * (H - t) * explicitScale H / H) := by
      have heq : explicitScale H * (3 * (H - t) * explicitScale H / H) =
          3 * (H - t) * explicitScale H ^ 2 / H := by ring
      rw [heq, hsqH]
      field_simp
      ring
    _ = (3 * (H - t) * explicitScale H / H) * explicitScale H := by ring

end PaperP1.ExplicitSaddleVariation
