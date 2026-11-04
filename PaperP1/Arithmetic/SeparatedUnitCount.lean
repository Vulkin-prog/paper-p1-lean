module

public import PaperP1.Arithmetic.NormalizedUnitCount

/-! # At most one exact height-one unit survives separated complete windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedUnitCount

open Finset PaperP1.Arithmetic PaperP1.NormalizedUnitCount

theorem height_one {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hsep : x + L ≤ y) :
    (units 1 1 x y L).card ≤ 1 := by
  apply card_le_one.mpr
  intro u hu v hv
  have huEq := mem_units.mp hu
  have hvEq := mem_units.mp hv
  simp only [one_mul] at huEq hvEq
  rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hy] at huEq hvEq
  have hu₁ := u.1.isLt
  have hu₂ := u.2.isLt
  have hv₁ := v.1.isLt
  have hv₂ := v.2.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

end PaperP1.SeparatedUnitCount
