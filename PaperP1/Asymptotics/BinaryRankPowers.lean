module

public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Critical-band decay from an actual linear lower bound on binary rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryRankPowers

def constant (C α d : ℝ) : ℝ := (2 : ℝ) ^ (d + α * C)

theorem constant_pos (C α d : ℝ) : 0 < constant C α d := Real.rpow_pos_of_pos (by norm_num) _

theorem upper {N L R : ℕ} {C α d : ℝ} (hN : 2 ≤ N) (hα : 0 ≤ α)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (hR : α * L - d ≤ (R : ℝ)) :
    (2 ^ R : ℝ)⁻¹ ≤ constant C α d * (N : ℝ) ^ (-α) := by
  have hlow : Real.log N / Real.log 2 - C ≤ (L : ℝ) := by have hh := (abs_le.mp hband).1; linarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hlow hlogtwo.le
  rw [sub_mul, div_mul_cancel₀ _ hlogtwo.ne'] at hmul
  have hscaled := mul_le_mul_of_nonneg_left hmul hα
  have hRmul := mul_le_mul_of_nonneg_right hR hlogtwo.le
  have hlog : Real.log 2 * (-(R : ℝ)) ≤ Real.log 2 * (d + α * C) + Real.log N * (-α) := by
    nlinarith only [hscaled, hRmul]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hinv : (2 ^ R : ℝ)⁻¹ = (2 : ℝ) ^ (-(R : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [hinv, constant]
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr hlog

end PaperP1.BinaryRankPowers
