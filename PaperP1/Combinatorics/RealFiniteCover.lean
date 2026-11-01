module

public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Cast.Order.Ring

/-! # Real-valued bounds for literal finite unions -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.RealFiniteCover

open Finset

theorem biUnion_card {ι V : Type*} [DecidableEq V] (S : Finset ι) (F : ι → Finset V)
    (B : ℝ) (hB : ∀ i ∈ S, ((F i).card : ℝ) ≤ B) :
    ((S.biUnion F).card : ℝ) ≤ (S.card : ℝ) * B := by
  calc
    _ ≤ ((∑ i ∈ S, (F i).card : ℕ) : ℝ) := by exact_mod_cast card_biUnion_le (s := S) (t := F)
    _ = ∑ i ∈ S, ((F i).card : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ _i ∈ S, B := sum_le_sum hB
    _ = _ := by simp

end PaperP1.RealFiniteCover
