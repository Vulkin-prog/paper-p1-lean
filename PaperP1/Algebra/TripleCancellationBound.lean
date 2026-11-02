module

public import PaperP1.Algebra.TripleCentering
public import Mathlib.Basic.Real.Basic

/-! # Incompatible triple activity has only independent and pair-activity costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleCancellationBound

open PaperP1.Algebra

theorem abs_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    _ ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := add_le_add (abs_add_le (a + b) c) le_rfl
    _ ≤ ((|a| + |b|) + |c|) + |d| := add_le_add (add_le_add (abs_add_le a b) le_rfl) le_rfl

theorem incompatible {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (q : Finset ι → ℝ)
    {x y z : ι} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h0 : q ∅ = 1) (hx : q {x} = p x) (hy : q {y} = p y) (hz : q {z} = p z)
    (hpx : 0 ≤ p x) (hpy : 0 ≤ p y) (hpz : 0 ≤ p z) (hq : q {x, y, z} = 0) :
    |centeredCoefficient p q {x, y, z}| ≤ p x * p y * p z +
      |centeredCoefficient p q {x, y}| * p z + |centeredCoefficient p q {x, z}| * p y +
      |centeredCoefficient p q {y, z}| * p x := by
  rw [TripleCentering.incompatible p q hxy hxz hyz h0 hx hy hz hq]
  simpa only [sub_eq_add_neg, neg_mul, abs_mul, abs_neg, abs_of_nonneg hpx,
    abs_of_nonneg hpy, abs_of_nonneg hpz] using
    abs_four (-p x * p y * p z) (-(centeredCoefficient p q {x, y} * p z))
      (-(centeredCoefficient p q {x, z} * p y)) (-(centeredCoefficient p q {y, z} * p x))

end PaperP1.TripleCancellationBound
