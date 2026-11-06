module

public import PaperP1.Analysis.P3StandardMonomialLimits
public import Mathlib.Analysis.Real.Sqrt

/-! # The actual integer cutoff and determinant divisor attain the sharp surface leading scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3SurfaceDivisorLimits

open Filter Topology P3StandardMonomialParameters

def cutoff (d e : ℕ) : ℕ := ⌊Real.sqrt (d : ℝ) * (e : ℝ)⌋₊

def divisor (d e : ℕ) : ℕ := cutoff d e * size d e - (cutoff d e + 2).choose 3

theorem cast_choose_shifted (L : ℕ) : ((L + 2).choose 3 : ℝ) =
    (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 6 := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_succ_right_eq (L + 2) 2)
  rw [show L + 2 - 2 = L by omega] at h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_choose_two] at h
  nlinarith only [h]

theorem cutoff_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ (cutoff d e : ℝ) / (e : ℝ)) atTop (𝓝 (Real.sqrt (d : ℝ))) := by
  simpa only [cutoff, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop (Real.sqrt_nonneg (d : ℝ))).comp tendsto_natCast_atTop_atTop

theorem choose_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ ((cutoff d e + 2).choose 3 : ℝ) / (e : ℝ) ^ 3)
      atTop (𝓝 (Real.sqrt (d : ℝ) ^ 3 / 6)) := by
  have hL := cutoff_ratio d
  have hi : Tendsto (fun e : ℕ ↦ (e : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := ((hL.mul (hL.add hi)).mul (hL.add (hi.const_mul 2))).div_const 6
  have he : Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) + 0) *
      (Real.sqrt (d : ℝ) + 2 * 0) / 6 = Real.sqrt (d : ℝ) ^ 3 / 6 := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  rw [cast_choose_shifted]
  field_simp [he0]

theorem raw_ratio (d : ℕ) :
    Tendsto (fun e : ℕ ↦ ((cutoff d e : ℝ) * (size d e : ℝ) - ((cutoff d e + 2).choose 3 : ℝ)) /
      (e : ℝ) ^ 3) atTop (𝓝 ((d : ℝ) * Real.sqrt (d : ℝ) / 3)) := by
  have h := ((cutoff_ratio d).mul (P3StandardMonomialLimits.size_ratio d)).sub (choose_ratio d)
  have hc : Real.sqrt (d : ℝ) * ((d : ℝ) / 2) - Real.sqrt (d : ℝ) ^ 3 / 6 =
      (d : ℝ) * Real.sqrt (d : ℝ) / 3 := by
    rw [pow_succ, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  field_simp [he0]

end PaperP1.P3SurfaceDivisorLimits
