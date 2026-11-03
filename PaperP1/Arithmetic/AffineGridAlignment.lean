module

public import PaperP1.Arithmetic.BoundedPointAlignment

/-! # An actual affine graph through two bounded integer grid points forces alignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineGridAlignment

def Aligned (B : ℕ) (X Y : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * B ∧ b ≤ 2 * B ∧
    |(b : ℤ) * X - (a : ℤ) * Y| ≤ ((a + b : ℕ) : ℤ) * B

theorem of_affine_grid (B : ℕ) (X Y : ℤ) (p q : ℤ × ℤ)
    (hX : (B : ℤ) < X) (hY : (B : ℤ) < Y)
    (hp : |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ))
    (hq : |q.1| ≤ (B : ℤ) ∧ |q.2| ≤ (B : ℤ)) (hpq : p ≠ q)
    (α β : ℚ) (hpLine : (p.2 : ℚ) = α * (p.1 : ℚ) + β)
    (hqLine : (q.2 : ℚ) = α * (q.1 : ℚ) + β)
    (hhost : (Y : ℚ) = α * (X : ℚ) + β) : Aligned B X Y := by
  have hcrossQ : ((q.1 : ℚ) - (p.1 : ℚ)) * ((Y : ℚ) - (p.2 : ℚ)) =
      ((q.2 : ℚ) - (p.2 : ℚ)) * ((X : ℚ) - (p.1 : ℚ)) := by
    rw [hpLine, hqLine, hhost]
    ring
  have hcross : (q.1 - p.1) * (Y - p.2) = (q.2 - p.2) * (X - p.1) := by
    exact_mod_cast hcrossQ
  exact BoundedPointAlignment.alignment_of_cross B X Y p q hX hY hp hq hpq hcross

theorem source_alignment {x y L : ℕ} (hL : 1 ≤ L)
    (h : Aligned (L + 1) (x : ℤ) (y : ℤ)) :
    CompressedTargetAlignment.Aligned 1 x y L :=
  BoundedPointAlignment.source_alignment hL h

theorem source_alignment_of_nonneg {X Y : ℤ} {L : ℕ} (hL : 1 ≤ L)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : Aligned (L + 1) X Y) :
    CompressedTargetAlignment.Aligned 1 X.natAbs Y.natAbs L := by
  apply source_alignment hL
  simpa only [Int.natCast_natAbs, abs_of_nonneg hX, abs_of_nonneg hY] using h

end PaperP1.AffineGridAlignment
