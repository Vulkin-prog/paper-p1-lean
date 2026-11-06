module

public import PaperP1.Algebra.P3ModelCoefficientGrowth

/-! # The original source model height absorbs quadratic branch shifts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalSourceModelHeight

theorem index_card_ge_four (d : ℕ) (hd : 0 < d) :
    4 ≤ Fintype.card (PaperP1.P3HomogeneousCoefficientFamily.Index d) := by
  rw [PaperP1.P3HomogeneousCoefficientFamily.index_card]
  exact (by decide : 4 ≤ Nat.choose 4 3).trans (Nat.choose_le_choose 3 (by omega : 4 ≤ d+3))

theorem exponent_pos (d : ℕ) (hd : 0 < d) : 0 < PaperP1.P3ModelCoefficientGrowth.exponent d := by
  unfold PaperP1.P3ModelCoefficientGrowth.exponent
  have hh := index_card_ge_four d hd
  exact Nat.mul_pos hd (by omega)

theorem height_le_model (d : ℕ) (hd : 0 < d) (H : ℕ) (hH : 1 ≤ H) :
    H ≤ PaperP1.P3ModelCoefficientGrowth.constant d * H ^ PaperP1.P3ModelCoefficientGrowth.exponent d := by
  have hp := le_self_pow hH (Nat.ne_of_gt (exponent_pos d hd))
  have hc := PaperP1.P3ModelCoefficientGrowth.constant_pos d
  exact hp.trans (by nlinarith)


theorem height_squared_le_model (d : ℕ) (hd : 0 < d) (H : ℕ) (hH : 1 ≤ H) :
    2 * H ^ 2 ≤ PaperP1.P3ModelCoefficientGrowth.constant d * H ^ PaperP1.P3ModelCoefficientGrowth.exponent d := by
  have hn := index_card_ge_four d hd
  have he : 2 ≤ PaperP1.P3ModelCoefficientGrowth.exponent d := by
    unfold PaperP1.P3ModelCoefficientGrowth.exponent
    have hh : 3 ≤ Fintype.card (PaperP1.P3HomogeneousCoefficientFamily.Index d) - 1 := by omega
    nlinarith
  have hc : 2 ≤ PaperP1.P3ModelCoefficientGrowth.constant d := by
    unfold PaperP1.P3ModelCoefficientGrowth.constant
    exact (by omega : 2 ≤ 3 * Fintype.card (PaperP1.P3HomogeneousCoefficientFamily.Index d)).trans
      (le_self_pow (by omega) (by omega))
  exact (Nat.mul_le_mul_right (H ^ 2) hc).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hH he))

end OriginalSourceModelHeight
