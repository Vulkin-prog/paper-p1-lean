module

public import PaperP1.Arithmetic.ExactUnitProgression
public import PaperP1.Algebra.BinaryEvenSelections
public import Mathlib.Data.Finset.Max

/-! # Canonical extreme selected units and their actual positive channel gap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedUnitExtrema

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.ChannelPlacements PaperP1.ExactUnitProgression

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure Bounds {a b x y L : ℕ} (S : Finset ↥(units a b x y L)) where
  first : ↥(units a b x y L)
  last : ↥(units a b x y L)
  first_mem : first ∈ S
  last_mem : last ∈ S
  first_le : ∀ u ∈ S, first.val.1 ≤ u.val.1
  le_last : ∀ u ∈ S, u.val.1 ≤ last.val.1

theorem bounds_nonempty {a b x y L : ℕ} (S : Finset ↥(units a b x y L)) (hS : S.Nonempty) :
    Nonempty (Bounds S) := by
  obtain ⟨u, hu, hmin⟩ := S.exists_min_image (fun u ↦ u.val.1) hS
  obtain ⟨v, hv, hmax⟩ := S.exists_max_image (fun u ↦ u.val.1) hS
  exact ⟨⟨u, v, hu, hv, hmin, hmax⟩⟩

def bounds {a b x y L : ℕ} (S : Finset ↥(units a b x y L)) (hS : S.Nonempty) : Bounds S :=
  Classical.choice (bounds_nonempty S hS)

theorem bounds_unique {a b x y L : ℕ} (ha : 0 < a) (hy : 0 < y)
    {S : Finset ↥(units a b x y L)} (A B : Bounds S) : A.first = B.first ∧ A.last = B.last := by
  constructor
  · apply left_projection_injective ha hy
    exact le_antisymm (A.first_le _ B.first_mem) (B.first_le _ A.first_mem)
  · apply left_projection_injective ha hy
    exact le_antisymm (B.le_last _ A.last_mem) (A.le_last _ B.last_mem)

theorem first_lt_last {a b x y L : ℕ} (ha : 0 < a) (hy : 0 < y)
    {S : Finset ↥(units a b x y L)} (hS : 2 ≤ S.card) (A : Bounds S) : A.first.val.1 < A.last.val.1 := by
  have hle := A.first_le _ A.last_mem
  apply lt_of_le_of_ne hle
  intro heq
  have hsub : S ⊆ {A.first} := by
    intro u hu
    apply mem_singleton.mpr
    apply left_projection_injective ha hy
    apply le_antisymm
    · exact (A.le_last _ hu).trans heq.symm.le
    · exact A.first_le _ hu
  have hc := card_le_card hsub
  simp only [card_singleton] at hc
  omega

theorem canonical_gap {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) {S : Finset ↥(units a b x y L)} (hS : 2 ≤ S.card) (A : Bounds S) :
    ∃ d ∈ Icc 1 (L / b),
      A.last.val.1.val = A.first.val.1.val + a * d ∧
      A.last.val.2.val = A.first.val.2.val + b * d ∧
      A.first.val.1.val ∈ placements L (a * d) ∧ A.first.val.2.val ∈ placements L (b * d) := by
  obtain ⟨d, hd, hleft, hright⟩ := positive_difference ha hab hx hy A.first A.last (first_lt_last ha hy hS A)
  obtain ⟨hi, hj⟩ := step_placements A.first A.last hleft hright
  exact ⟨d, mem_Icc.mpr ⟨by omega, gap_bound hb A.first A.last hright⟩, hleft, hright, hi, hj⟩

theorem gap_unique {a b x y L d e : ℕ} (ha : 0 < a) {S : Finset ↥(units a b x y L)} (A : Bounds S)
    (hd : A.last.val.1.val = A.first.val.1.val + a * d)
    (he : A.last.val.1.val = A.first.val.1.val + a * e) : d = e := by
  exact Nat.eq_of_mul_eq_mul_left ha (Nat.add_left_cancel (hd.symm.trans he))

theorem selected_position {a b x y L d : ℕ} (ha : 0 < a) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) {S : Finset ↥(units a b x y L)} (A : Bounds S)
    (hd : A.last.val.1.val = A.first.val.1.val + a * d) (u : ↥(units a b x y L)) (hu : u ∈ S) :
    ∃ k ≤ d, u.val.1.val = A.first.val.1.val + a * k ∧ u.val.2.val = A.first.val.2.val + b * k := by
  obtain ⟨k, hleft, hright⟩ := ordered_difference ha hab hx hy A.first u (A.first_le _ hu)
  refine ⟨k, ?_, hleft, hright⟩
  have hle : u.val.1.val ≤ A.last.val.1.val := A.le_last _ hu
  have hmul : a * k ≤ a * d := by omega
  exact Nat.le_of_mul_le_mul_left hmul ha

theorem selected_eq_stepUnit {a b x y L d : ℕ} (ha : 0 < a) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) {S : Finset ↥(units a b x y L)} (A : Bounds S)
    (hd : A.last.val.1.val = A.first.val.1.val + a * d)
    (hfitX : A.first.val.1.val + a * d ≤ L) (hfitY : A.first.val.2.val + b * d ≤ L)
    (u : ↥(units a b x y L)) (hu : u ∈ S) :
    ∃ k : Fin (d + 1), u = stepUnit (by omega) hy A.first k.val
      (by have hk := k.isLt; nlinarith) (by have hk := k.isLt; nlinarith) := by
  obtain ⟨k, hk, hleft, hright⟩ := selected_position ha hab hx hy A hd u hu
  refine ⟨⟨k, by omega⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact hleft
  · exact hright

end PaperP1.SelectedUnitExtrema
