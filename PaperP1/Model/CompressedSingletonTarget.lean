module

public import PaperP1.Model.PairPrimitiveCompression
public import PaperP1.Model.OneTargetCrossing

/-! # A singleton primitive compressed extension has exactly the original crossing rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedSingletonTarget

open Finset PaperP1.Model

theorem nullity_eq_rank (L : ℕ) (e : Finset ℕ) (z : ℕ)
    (hp : PairPrimitiveCompression.Primitive L e {z}) :
    PairPrimitiveCompression.nullity L e {z} = OneTargetCrossing.rank e L z := by
  have hfresh : z ∉ e := disjoint_singleton_right.mp hp.1
  have hfirst := PairPrimitiveCompression.union_nullity L e {z} hp
  rw [union_singleton] at hfirst
  have hsecond := OneTargetCrossing.nullity_insert e L z hfresh
  omega

theorem rank_pos (L : ℕ) (e : Finset ℕ) (z : ℕ)
    (hp : PairPrimitiveCompression.Primitive L e {z}) : 0 < OneTargetCrossing.rank e L z := by
  rw [← nullity_eq_rank L e z hp]
  exact hp.2.2.1

end PaperP1.CompressedSingletonTarget
