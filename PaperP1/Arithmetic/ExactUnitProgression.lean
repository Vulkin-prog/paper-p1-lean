module

public import PaperP1.Arithmetic.ExactMatchCongruences
public import PaperP1.Arithmetic.ChannelPlacements

/-! # Actual exact units have the primitive step (a,b), with every intermediate unit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactUnitProgression

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.ChannelPlacements

theorem left_projection_injective {a b x y L : ℕ} (ha : 0 < a) (hy : 0 < y) :
    Function.Injective (fun u : ↥(units a b x y L) ↦ u.val.1) := by
  intro u v heq
  change u.val.1 = v.val.1 at heq
  apply Subtype.ext
  refine Prod.ext heq ?_
  apply startCompleteVertexLabel_injective hy
  apply mul_left_cancel₀ ha.ne'
  rw [← mem_units.mp u.property, ← mem_units.mp v.property, heq]

theorem ordered_difference {a b x y L : ℕ} (ha : 0 < a) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) (u v : ↥(units a b x y L)) (huv : u.val.1 ≤ v.val.1) :
    ∃ d : ℕ, v.val.1.val = u.val.1.val + a * d ∧ v.val.2.val = u.val.2.val + b * d := by
  obtain ⟨tu, _, hxu, hyu⟩ := ExactMatchCongruences.source_parameter ha hab hx _ _ (mem_units.mp u.property)
  obtain ⟨tv, _, hxv, hyv⟩ := ExactMatchCongruences.source_parameter ha hab hx _ _ (mem_units.mp v.property)
  rw [startCompleteVertexLabel_eq_offset (by omega)] at hxu hxv
  rw [startCompleteVertexLabel_eq_offset hy] at hyu hyv
  have hle : a * tu ≤ a * tv := by have hval : u.val.1.val ≤ v.val.1.val := huv; omega
  have ht : tu ≤ tv := Nat.le_of_mul_le_mul_left hle ha
  refine ⟨tv - tu, ?_, ?_⟩
  · have hmul : a * tv = a * tu + a * (tv - tu) := by rw [← mul_add, Nat.add_sub_of_le ht]
    omega
  · have hmul : b * tv = b * tu + b * (tv - tu) := by rw [← mul_add, Nat.add_sub_of_le ht]
    omega

theorem positive_difference {a b x y L : ℕ} (ha : 0 < a) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) (u v : ↥(units a b x y L)) (huv : u.val.1 < v.val.1) :
    ∃ d : ℕ, 0 < d ∧ v.val.1.val = u.val.1.val + a * d ∧ v.val.2.val = u.val.2.val + b * d := by
  obtain ⟨d, hleft, hright⟩ := ordered_difference ha hab hx hy u v huv.le
  refine ⟨d, ?_, hleft, hright⟩
  have hlt : u.val.1.val < v.val.1.val := huv
  by_contra hd
  have : d = 0 := by omega
  simp only [this, mul_zero, add_zero] at hleft
  omega

def stepUnit {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    (u : ↥(units a b x y L)) (k : ℕ)
    (hleft : u.val.1.val + a * k ≤ L) (hright : u.val.2.val + b * k ≤ L) : ↥(units a b x y L) :=
  ⟨(⟨u.val.1.val + a * k, by omega⟩, ⟨u.val.2.val + b * k, by omega⟩), by
    apply mem_units.mpr
    have hunit := mem_units.mp u.property
    rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hy] at hunit ⊢
    dsimp only
    nlinarith⟩

theorem stepUnit_injective {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (u : ↥(units a b x y L)) (k l : ℕ) (hk₁ : u.val.1.val + a * k ≤ L)
    (hk₂ : u.val.2.val + b * k ≤ L) (hl₁ : u.val.1.val + a * l ≤ L) (hl₂ : u.val.2.val + b * l ≤ L)
    (h : stepUnit hx hy u k hk₁ hk₂ = stepUnit hx hy u l hl₁ hl₂) : k = l := by
  have hv := congrArg (fun v : ↥(units a b x y L) ↦ v.val.1.val) h
  change u.val.1.val + a * k = u.val.1.val + a * l at hv
  exact Nat.eq_of_mul_eq_mul_left ha (Nat.add_left_cancel hv)

theorem step_placements {a b x y L d : ℕ} (u v : ↥(units a b x y L))
    (hleft : v.val.1.val = u.val.1.val + a * d) (hright : v.val.2.val = u.val.2.val + b * d) :
    u.val.1.val ∈ placements L (a * d) ∧ u.val.2.val ∈ placements L (b * d) := by
  have hi := v.val.1.isLt
  have hj := v.val.2.isLt
  constructor
  · have hfit : a * d ≤ L := by omega
    simp only [placements, ite_eq_left hfit, mem_range]
    omega
  · have hfit : b * d ≤ L := by omega
    simp only [placements, ite_eq_left hfit, mem_range]
    omega

theorem gap_bound {a b x y L d : ℕ} (hb : 0 < b) (u v : ↥(units a b x y L))
    (hright : v.val.2.val = u.val.2.val + b * d) : d ≤ L / b := by
  apply (Nat.le_div_iff_mul_le hb).mpr
  have hj := v.val.2.isLt
  nlinarith

end PaperP1.ExactUnitProgression
