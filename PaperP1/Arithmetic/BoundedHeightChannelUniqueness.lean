module

public import PaperP1.Arithmetic.SmallChannelUniqueness

/-! # Reduced enlarged channels are unique at every polynomial height

The determinant argument keeps its exact height-dependent source threshold.
It applies to every geometric channel, including pairs with no exact unit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedHeightChannelUniqueness

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount

theorem same_slope (a b c d x y L Q : ℕ)
    (ha : a ≤ Q) (hb : b ≤ Q)
    (hc : c ≤ Q) (hd : d ≤ Q)
    (hlarge : 4 * Q ^ 2 * (L + 1) < y)
    (h₁ : EnlargedPairGeometry.Geometric a b x y L)
    (h₂ : EnlargedPairGeometry.Geometric c d x y L) : a * d = b * c := by
  have hnum : d * (a + b) * (L + 1) + b * (c + d) * (L + 1) ≤ 4 * Q ^ 2 * (L + 1) := by
    have h₃ := Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul hd (show a + b ≤ 2 * Q by omega))
    have h₄ := Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul hb (show c + d ≤ 2 * Q by omega))
    nlinarith only [h₃, h₄]
  have heq : ((b : ℤ) * c - (a : ℤ) * d) * y =
      (d : ℤ) * ((b : ℤ) * x - (a : ℤ) * y) -
        (b : ℤ) * ((d : ℤ) * x - (c : ℤ) * y) := by ring
  have hbound : |((b : ℤ) * c - (a : ℤ) * d) * y| ≤ ((4 * Q ^ 2 * (L + 1) : ℕ) : ℤ) := by
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
        have hn : d * ((a + b) * (L + 1)) + b * ((c + d) * (L + 1)) ≤ 4 * Q ^ 2 * (L + 1) := by
          simpa only [mul_assoc] using hnum
        exact_mod_cast hn
  have hdet : (b : ℤ) * c - (a : ℤ) * d = 0 := by
    by_contra hne
    have hone := Int.one_le_abs hne
    have hy : (y : ℤ) ≤ |((b : ℤ) * c - (a : ℤ) * d) * y| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) y)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (Nat.cast_nonneg (α := ℤ) y)
    have hylarge : ((4 * Q ^ 2 * (L + 1) : ℕ) : ℤ) < y := by exact_mod_cast hlarge
    omega
  have hcast : ((a * d : ℕ) : ℤ) = ((b * c : ℕ) : ℤ) := by push_cast; linarith only [hdet]
  exact_mod_cast hcast


theorem reduced_eq {a b c d : ℕ} (ha : 0 < a) (hab : a.Coprime b) (hcd : c.Coprime d)
    (hslope : a * d = b * c) : a = c ∧ b = d := by
  have hac : a ∣ c := hab.dvd_mul_left.mp (hslope ▸ dvd_mul_right a d)
  have hca : c ∣ a := hcd.dvd_mul_right.mp (hslope.symm ▸ dvd_mul_left c b)
  have heq : a = c := Nat.dvd_antisymm hac hca
  have hprod : a * d = a * b := by simpa only [← heq, mul_comm b a] using hslope
  exact ⟨heq, (Nat.eq_of_mul_eq_mul_left ha hprod).symm⟩

theorem unique {a b c d x y L Q : ℕ} (ha : 0 < a) (hab : a.Coprime b) (hcd : c.Coprime d)
    (haQ : a ≤ Q) (hbQ : b ≤ Q) (hcQ : c ≤ Q) (hdQ : d ≤ Q)
    (hlarge : 4 * Q ^ 2 * (L + 1) < y)
    (h₁ : PaperP1.EnlargedPairGeometry.Geometric a b x y L)
    (h₂ : PaperP1.EnlargedPairGeometry.Geometric c d x y L) : a = c ∧ b = d :=
  reduced_eq ha hab hcd (same_slope a b c d x y L Q haQ hbQ hcQ hdQ hlarge h₁ h₂)

end PaperP1.BoundedHeightChannelUniqueness
