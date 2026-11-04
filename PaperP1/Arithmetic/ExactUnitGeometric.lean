module

public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Every literal exact unit yields the enlarged geometric channel

This finite implication holds on every positive source interval.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactUnitGeometric

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount PaperP1.EnlargedPairGeometry

theorem of_unit {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    {u : Fin (L + 1) × Fin (L + 1)} (hu : u ∈ units a b x y L) : Geometric a b x y L := by
  have he := congrArg (fun n : ℕ ↦ (n : ℤ)) (mem_units.mp hu)
  push_cast at he
  rw [label_cast hx, label_cast hy] at he
  have hdiff : (b : ℤ) * x - (a : ℤ) * y = (a : ℤ) * offset u.2 - (b : ℤ) * offset u.1 := by nlinarith only [he]
  unfold Geometric
  rw [hdiff]
  calc
    _ ≤ |(a : ℤ) * offset u.2| + |(b : ℤ) * offset u.1| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ((a : ℤ) * offset u.2) 0 ((b : ℤ) * offset u.1)
    _ = (a : ℤ) * |offset u.2| + (b : ℤ) * |offset u.1| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) a), abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b)]
    _ ≤ (a : ℤ) * ((L + 1 : ℕ) : ℤ) + (b : ℤ) * ((L + 1 : ℕ) : ℤ) :=
      add_le_add (mul_le_mul_of_nonneg_left (offset_abs u.2) (Nat.cast_nonneg a))
        (mul_le_mul_of_nonneg_left (offset_abs u.1) (Nat.cast_nonneg b))
    _ = _ := by push_cast; ring

theorem of_nonempty {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hu : (units a b x y L).Nonempty) : Geometric a b x y L := by
  obtain ⟨u, hu⟩ := hu
  exact of_unit hx hy hu

end PaperP1.ExactUnitGeometric
