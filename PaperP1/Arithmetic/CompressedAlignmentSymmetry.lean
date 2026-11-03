module

public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # Literal compressed-target alignment is symmetric when the width multiplier is fixed -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.CompressedAlignmentSymmetry

theorem symm {D X z L : ℕ} (h : CompressedTargetAlignment.Aligned D X z L) :
    CompressedTargetAlignment.Aligned D z X L := by
  obtain ⟨r, s, hr, hs, hcop, hrB, hsB, hgeom⟩ := h
  refine ⟨s, r, hs, hr, hcop.symm, hsB, hrB, ?_⟩
  calc
    |(s : ℤ) * X - (r : ℤ) * z| = |(r : ℤ) * z - (s : ℤ) * X| := abs_sub_comm _ _
    _ ≤ ((r + s : ℕ) : ℤ) * ((D * (L + 1) : ℕ) : ℤ) := hgeom
    _ = _ := by rw [Nat.add_comm r s]

end PaperP1.CompressedAlignmentSymmetry
