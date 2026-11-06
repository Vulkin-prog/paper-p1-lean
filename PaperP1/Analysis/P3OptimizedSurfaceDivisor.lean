module

public import PaperP1.Analysis.P3SurfaceDivisorLimits

/-! # The actual natural determinant exponent has the sharp weight/divisor ratio -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3OptimizedSurfaceDivisor

open Filter Topology P3StandardMonomialParameters P3SurfaceDivisorLimits

theorem cast_divisor_eventually (d : ℕ) (hd : 0 < d) :
    ∀ᶠ e : ℕ in atTop,
      (divisor d e : ℝ) = (cutoff d e : ℝ) * (size d e : ℝ) - ((cutoff d e + 2).choose 3 : ℝ) ∧
        0 < divisor d e := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < (d : ℝ) * Real.sqrt (d : ℝ) / 3 := by positivity
  have hp := (raw_ratio d).eventually (Ioi_mem_nhds hc)
  filter_upwards [hp, eventually_ge_atTop 1] with e he h1
  have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hraw : 0 < (cutoff d e : ℝ) * (size d e : ℝ) - ((cutoff d e + 2).choose 3 : ℝ) := by
    simpa only [zero_mul] using (lt_div_iff₀ (pow_pos heR 3)).mp he
  have hn : (cutoff d e + 2).choose 3 < cutoff d e * size d e := by exact_mod_cast (sub_pos.mp hraw)
  refine ⟨?_, Nat.sub_pos_iff_lt.mpr hn⟩
  dsimp only [divisor]
  rw [Nat.cast_sub hn.le, Nat.cast_mul]

theorem divisor_ratio (d : ℕ) (hd : 0 < d) :
    Tendsto (fun e : ℕ ↦ (divisor d e : ℝ) / (e : ℝ) ^ 3)
      atTop (𝓝 ((d : ℝ) * Real.sqrt (d : ℝ) / 3)) := by
  apply (raw_ratio d).congr'
  filter_upwards [cast_divisor_eventually d hd] with e he
  rw [he.1]

theorem weight_divisor_ratio (d : ℕ) (hd : 0 < d) :
    Tendsto (fun e : ℕ ↦ (weight d e : ℝ) / (divisor d e : ℝ))
      atTop (𝓝 (1 / Real.sqrt (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hc : (d : ℝ) * Real.sqrt (d : ℝ) / 3 ≠ 0 := by positivity
  have h := (P3StandardMonomialLimits.weight_ratio d).div (divisor_ratio d hd) hc
  have he : ((d : ℝ) / 3) / ((d : ℝ) * Real.sqrt (d : ℝ) / 3) = 1 / Real.sqrt (d : ℝ) := by
    field_simp [hdR.ne', hs.ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1, cast_divisor_eventually d hd] with e h1 he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hE0 : (divisor d e : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he.2)
  change ((weight d e : ℝ) / (e : ℝ) ^ 3) / ((divisor d e : ℝ) / (e : ℝ) ^ 3) =
    (weight d e : ℝ) / (divisor d e : ℝ)
  field_simp [he0, hE0]

theorem exists_parameters (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ℕ, d ≤ e ∧ 0 < divisor d e ∧
      (weight d e : ℝ) < (1 / Real.sqrt (d : ℝ) + ε) * (divisor d e : ℝ) := by
  have hp := (weight_divisor_ratio d hd).eventually
    (Iio_mem_nhds (lt_add_of_pos_right (1 / Real.sqrt (d : ℝ)) hε))
  have hev : ∀ᶠ e : ℕ in atTop, d ≤ e ∧ 0 < divisor d e ∧
      (weight d e : ℝ) < (1 / Real.sqrt (d : ℝ) + ε) * (divisor d e : ℝ) := by
    filter_upwards [eventually_ge_atTop d, cast_divisor_eventually d hd, hp] with e he hE hratio
    have hpos : (0 : ℝ) < divisor d e := by exact_mod_cast hE.2
    exact ⟨he, hE.2, (div_lt_iff₀ hpos).mp hratio⟩
  exact hev.exists

end PaperP1.P3OptimizedSurfaceDivisor
