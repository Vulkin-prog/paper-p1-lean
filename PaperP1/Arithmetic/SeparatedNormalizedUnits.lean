module

public import PaperP1.Arithmetic.NormalizedUnitCount
public import Mathlib.Data.Nat.Dist

/-! # The height-one rational code vanishes for separated complete windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedNormalizedUnits

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount

theorem units_empty {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hsep : L < Nat.dist x y) :
    units 1 1 x y L = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  have heq := mem_units.mp hu
  simp only [one_mul] at heq
  rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hy] at heq
  have hi := u.1.isLt
  have hj := u.2.isLt
  unfold Nat.dist at hsep
  omega

theorem rational_weight_zero {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hsep : L < Nat.dist x y) :
    (2 ^ ((units 1 1 x y L).card - 1) : ℝ) - 1 = 0 := by
  rw [units_empty hx hy hsep, card_empty]
  norm_num

end PaperP1.SeparatedNormalizedUnits
