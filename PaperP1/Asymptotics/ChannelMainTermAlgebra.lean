module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Elementary transfer of positive main-term factors to their channel scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelMainTermAlgebra

theorem main_term_scale {N L P W S w cs Cs PL PU QL QU β : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hP : 0 ≤ P) (hw : 0 ≤ w)
    (hcs : 0 ≤ cs) (hCs : 0 ≤ Cs) (hQL : 0 ≤ QL) (hPU : 0 ≤ PU)
    (hPlo : PL * N ^ (-2 : ℝ) ≤ P) (hPhi : P ≤ PU * N ^ (-2 : ℝ))
    (hWlo : QL * N ^ β ≤ W) (hWhi : W ≤ QU * N ^ β)
    (hSlo : cs * L * W ≤ S) (hShi : S ≤ Cs * L * W) :
    (PL * w * cs * QL) * L * N ^ (-1 + β) ≤ P * N * w * S ∧
      P * N * w * S ≤ (PU * w * Cs * QU) * L * N ^ (-1 + β) := by
  have hW : 0 ≤ W := (mul_nonneg hQL (Real.rpow_nonneg hN.le _)).trans hWlo
  have hS : 0 ≤ S := (mul_nonneg (mul_nonneg hcs hL) hW).trans hSlo
  have hp : N ^ (-2 : ℝ) * N * N ^ β = N ^ (-1 + β) := by
    calc
      _ = N ^ (-2 : ℝ) * N ^ (1 : ℝ) * N ^ β := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN, ← Real.rpow_add hN]; congr 1; ring
  have hSL : cs * L * (QL * N ^ β) ≤ S :=
    (mul_le_mul_of_nonneg_left hWlo (mul_nonneg hcs hL)).trans hSlo
  have hSU : S ≤ Cs * L * (QU * N ^ β) :=
    hShi.trans (mul_le_mul_of_nonneg_left hWhi (mul_nonneg hCs hL))
  have hPL : (PL * N ^ (-2 : ℝ)) * N * w ≤ P * N * w :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPlo hN.le) hw
  have hPU' : P * N * w ≤ (PU * N ^ (-2 : ℝ)) * N * w :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPhi hN.le) hw
  constructor
  · calc
      _ = (PL * w * cs * QL) * L * (N ^ (-2 : ℝ) * N * N ^ β) := by rw [hp]
      _ = ((PL * N ^ (-2 : ℝ)) * N * w) * (cs * L * (QL * N ^ β)) := by ring
      _ ≤ _ := mul_le_mul hPL hSL (by positivity) (by positivity)
  · calc
      _ ≤ ((PU * N ^ (-2 : ℝ)) * N * w) * (Cs * L * (QU * N ^ β)) :=
        mul_le_mul hPU' hSU hS (by positivity)
      _ = (PU * w * Cs * QU) * L * (N ^ (-2 : ℝ) * N * N ^ β) := by ring
      _ = _ := by rw [hp]

end PaperP1.ChannelMainTermAlgebra
