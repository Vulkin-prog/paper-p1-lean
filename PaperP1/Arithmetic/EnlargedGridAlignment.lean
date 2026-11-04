module

public import PaperP1.Arithmetic.AffineGridAlignment

/-! # Alignment exclusions that retain the actual enlarged offset width

The slope height remains the original cubic height. Only the displacement
radius grows with the two physical widths.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedGridAlignment

theorem radius_mono {D E x y L : ℕ} (hDE : D ≤ E)
    (h : CompressedTargetAlignment.Aligned D x y L) :
    CompressedTargetAlignment.Aligned E x y L := by
  obtain ⟨r, s, hr, hs, hcop, hrB, hsB, he⟩ := h
  refine ⟨r, s, hr, hs, hcop, hrB, hsB, he.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Nat.mul_le_mul_right (L + 1) hDE)
    (Nat.cast_nonneg (r + s))

theorem of_grid {D W L : ℕ} {X Y : ℤ}
    (hwidth : W ≤ D * (L + 1)) (hheight : 2 * W ≤ (L + 1) ^ 3)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : AffineGridAlignment.Aligned W X Y) :
    CompressedTargetAlignment.Aligned D X.natAbs Y.natAbs L := by
  obtain ⟨a, b, ha, hb, hcop, haB, hbB, he⟩ := h
  refine ⟨a, b, ha, hb, hcop, haB.trans hheight, hbB.trans hheight, ?_⟩
  have he' : |(b : ℤ) * X - (a : ℤ) * Y| ≤
      ((a + b : ℕ) : ℤ) * ((D * (L + 1) : ℕ) : ℤ) :=
    he.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hwidth) (Nat.cast_nonneg (a + b)))
  simpa only [Int.natCast_natAbs, abs_of_nonneg hX, abs_of_nonneg hY, abs_sub_comm] using he'

theorem of_affine_grid {D W L : ℕ} {X Y : ℤ}
    (hwidth : W ≤ D * (L + 1)) (hheight : 2 * W ≤ (L + 1) ^ 3)
    (hX : (W : ℤ) < X) (hY : (W : ℤ) < Y)
    (p q : ℤ × ℤ) (hp : |p.1| ≤ (W : ℤ) ∧ |p.2| ≤ (W : ℤ))
    (hq : |q.1| ≤ (W : ℤ) ∧ |q.2| ≤ (W : ℤ)) (hpq : p ≠ q)
    (α β : ℚ) (hpLine : (p.2 : ℚ) = α * (p.1 : ℚ) + β)
    (hqLine : (q.2 : ℚ) = α * (q.1 : ℚ) + β)
    (hhost : (Y : ℚ) = α * (X : ℚ) + β) :
    CompressedTargetAlignment.Aligned D X.natAbs Y.natAbs L := by
  exact of_grid hwidth hheight ((Nat.cast_nonneg W).trans hX.le)
    ((Nat.cast_nonneg W).trans hY.le)
    (AffineGridAlignment.of_affine_grid W X Y p q hX hY hp hq hpq α β hpLine hqLine hhost)

theorem of_exact_match {Dold Dnew x y L r s : ℕ} {i j : ℤ}
    (hr : 0 < r) (hs : 0 < s) (hcop : r.Coprime s)
    (hrB : r ≤ (L + 1) ^ 3) (hsB : s ≤ (L + 1) ^ 3)
    (hi : |i| ≤ ((Dold * (L + 1) : ℕ) : ℤ))
    (hj : |j| ≤ ((Dnew * (L + 1) : ℕ) : ℤ))
    (he : (r : ℤ) * ((y : ℤ) + j) = (s : ℤ) * ((x : ℤ) + i)) :
    CompressedTargetAlignment.Aligned (max Dold Dnew) x y L := by
  refine ⟨r, s, hr, hs, hcop, hrB, hsB, ?_⟩
  have hi' : |i| ≤ ((max Dold Dnew * (L + 1) : ℕ) : ℤ) :=
    hi.trans (by exact_mod_cast Nat.mul_le_mul_right (L + 1) (le_max_left Dold Dnew))
  have hj' : |j| ≤ ((max Dold Dnew * (L + 1) : ℕ) : ℤ) :=
    hj.trans (by exact_mod_cast Nat.mul_le_mul_right (L + 1) (le_max_right Dold Dnew))
  have heq : (r : ℤ) * y - (s : ℤ) * x = (s : ℤ) * i - (r : ℤ) * j := by
    linarith only [he]
  rw [heq]
  calc
    _ ≤ |(s : ℤ) * i| + |(r : ℤ) * j| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ((s : ℤ) * i) 0 ((r : ℤ) * j)
    _ = (s : ℤ) * |i| + (r : ℤ) * |j| := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) r),
        abs_of_nonneg (Nat.cast_nonneg (α := ℤ) s)]
    _ ≤ (s : ℤ) * ((max Dold Dnew * (L + 1) : ℕ) : ℤ) +
        (r : ℤ) * ((max Dold Dnew * (L + 1) : ℕ) : ℤ) :=
      add_le_add (mul_le_mul_of_nonneg_left hi' (Nat.cast_nonneg s))
        (mul_le_mul_of_nonneg_left hj' (Nat.cast_nonneg r))
    _ = _ := by push_cast; ring

end PaperP1.EnlargedGridAlignment
