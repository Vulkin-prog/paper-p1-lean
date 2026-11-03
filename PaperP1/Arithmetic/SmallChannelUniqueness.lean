module

public import PaperP1.Arithmetic.SmallExactUnitAlignment

/-! # A distant window pair admits only one small rational alignment slope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallChannelUniqueness

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount

theorem same_slope (a b c d x y L : ℕ)
    (ha : a ≤ 2 * (L + 1)) (hb : b ≤ 2 * (L + 1))
    (hc : c ≤ 2 * (L + 1)) (hd : d ≤ 2 * (L + 1))
    (hlarge : 16 * (L + 1) ^ 3 < y)
    (h₁ : EnlargedPairGeometry.Geometric a b x y L)
    (h₂ : EnlargedPairGeometry.Geometric c d x y L) : a * d = b * c := by
  have hnum : d * (a + b) * (L + 1) + b * (c + d) * (L + 1) ≤ 16 * (L + 1) ^ 3 := by
    have h₃ := Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul hd (show a + b ≤ 4 * (L + 1) by omega))
    have h₄ := Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul hb (show c + d ≤ 4 * (L + 1) by omega))
    nlinarith only [h₃, h₄]
  have heq : ((b : ℤ) * c - (a : ℤ) * d) * y =
      (d : ℤ) * ((b : ℤ) * x - (a : ℤ) * y) -
        (b : ℤ) * ((d : ℤ) * x - (c : ℤ) * y) := by ring
  have hbound : |((b : ℤ) * c - (a : ℤ) * d) * y| ≤ ((16 * (L + 1) ^ 3 : ℕ) : ℤ) := by
    calc
      _ = |(d : ℤ) * ((b : ℤ) * x - (a : ℤ) * y) -
          (b : ℤ) * ((d : ℤ) * x - (c : ℤ) * y)| := congrArg abs heq
      _ ≤ |(d : ℤ) * ((b : ℤ) * x - (a : ℤ) * y)| +
          |(b : ℤ) * ((d : ℤ) * x - (c : ℤ) * y)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((d : ℤ) * ((b : ℤ) * x - (a : ℤ) * y)) 0
            ((b : ℤ) * ((d : ℤ) * x - (c : ℤ) * y))
      _ = (d : ℤ) * |(b : ℤ) * x - (a : ℤ) * y| +
          (b : ℤ) * |(d : ℤ) * x - (c : ℤ) * y| := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) d),
          abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b)]
      _ ≤ (d : ℤ) * (((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ)) +
          (b : ℤ) * (((c + d : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ)) := add_le_add
        (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg d))
        (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg b))
      _ ≤ _ := by
        have hn : d * ((a + b) * (L + 1)) + b * ((c + d) * (L + 1)) ≤ 16 * (L + 1) ^ 3 := by
          simpa only [mul_assoc] using hnum
        exact_mod_cast hn
  have hdet : (b : ℤ) * c - (a : ℤ) * d = 0 := by
    by_contra hne
    have hone := Int.one_le_abs hne
    have hy : (y : ℤ) ≤ |((b : ℤ) * c - (a : ℤ) * d) * y| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) y)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (Nat.cast_nonneg (α := ℤ) y)
    have hylarge : ((16 * (L + 1) ^ 3 : ℕ) : ℤ) < y := by exact_mod_cast hlarge
    omega
  have hcast : ((a * d : ℕ) : ℤ) = ((b * c : ℕ) : ℤ) := by push_cast; linarith only [hdet]
  exact_mod_cast hcast

theorem units_eq_of_slope {a b c d x y L : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hslope : a * d = b * c) : units a b x y L = units c d x y L := by
  ext u
  rw [mem_units, mem_units]
  constructor
  · intro he
    apply mul_left_cancel₀ ha.ne'
    calc
      a * (d * startCompleteVertexLabel x L u.1) = (a * d) * startCompleteVertexLabel x L u.1 := by ring
      _ = (b * c) * startCompleteVertexLabel x L u.1 := by rw [hslope]
      _ = c * (b * startCompleteVertexLabel x L u.1) := by ring
      _ = c * (a * startCompleteVertexLabel y L u.2) := by rw [he]
      _ = a * (c * startCompleteVertexLabel y L u.2) := by ring
  · intro he
    apply mul_left_cancel₀ hd.ne'
    calc
      d * (b * startCompleteVertexLabel x L u.1) = b * (d * startCompleteVertexLabel x L u.1) := by ring
      _ = b * (c * startCompleteVertexLabel y L u.2) := by rw [he]
      _ = (b * c) * startCompleteVertexLabel y L u.2 := by ring
      _ = (a * d) * startCompleteVertexLabel y L u.2 := by rw [hslope]
      _ = d * (a * startCompleteVertexLabel y L u.2) := by ring

theorem unit_geometric {N a b x y L : ℕ} (hN : 0 < N)
    (hx : x ∈ Model.dyadicBlock N) (hy : y ∈ Model.dyadicBlock N)
    (hu : (units a b x y L).Nonempty) : EnlargedPairGeometry.Geometric a b x y L := by
  have hsource : (x, y) ∈ FixedChannelSourceGeometry.unitSources N a b L :=
    mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hu⟩
  have hh := FixedChannelLinearCount.unit_alignment (a := a) (b := b) (L := L) (xy := (x, y)) hN hsource
  simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hh

end PaperP1.SmallChannelUniqueness
