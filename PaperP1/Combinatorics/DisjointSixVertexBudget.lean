module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Ring.Nat
public import Lean.Elab.Tactic.Omega

/-! # Exact six-vertex packing, with an explicit cost for components of size at most five -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointSixVertexBudget

open Finset

variable {V : Type*} [DecidableEq V]

theorem surviving_size (U D : Finset V) (F : Finset (Finset V)) (hDU : D ⊆ U)
    (hF : (↑F : Set (Finset V)).PairwiseDisjoint id)
    (hFU : ∀ E ∈ F, E ⊆ U) (hFD : ∀ E ∈ F, Disjoint E D) :
    (∑ E ∈ F, E.card) + D.card ≤ U.card := by
  have hUD : Disjoint (F.biUnion id) D := by
    apply disjoint_left.mpr
    intro v hv hD
    obtain ⟨E, hE, hvE⟩ := mem_biUnion.mp hv
    exact disjoint_left.mp (hFD E hE) hvE hD
  have hsub : F.biUnion id ∪ D ⊆ U := by
    intro v hv
    obtain hv | hv := mem_union.mp hv
    · obtain ⟨E, hE, hvE⟩ := mem_biUnion.mp hv
      exact hFU E hE hvE
    · exact hDU hv
  have hsum : (F.biUnion id).card = ∑ E ∈ F, E.card := by
    simpa only [id_eq] using card_biUnion hF
  have hh := card_le_card hsub
  rwa [card_union_of_disjoint hUD, hsum] at hh

theorem six_vertex_budget (U D : Finset V) (F : Finset (Finset V)) (hDU : D ⊆ U)
    (hF : (↑F : Set (Finset V)).PairwiseDisjoint id)
    (hFU : ∀ E ∈ F, E ⊆ U) (hFD : ∀ E ∈ F, Disjoint E D)
    (hthree : ∀ E ∈ F, 3 ≤ E.card) :
    6 * F.card + D.card ≤ U.card + 3 * (F.filter fun E ↦ E.card ≤ 5).card := by
  have hsize := surviving_size U D F hDU hF hFU hFD
  have hpoint (E : Finset V) (hE : E ∈ F) : 6 ≤ E.card + if E.card ≤ 5 then 3 else 0 := by
    have hh := hthree E hE
    split_ifs <;> omega
  have hsum : 6 * F.card ≤ (∑ E ∈ F, E.card) + 3 * (F.filter fun E ↦ E.card ≤ 5).card := by
    have hh := sum_le_sum hpoint
    have hsmall : (∑ E ∈ F, if E.card ≤ 5 then 3 else 0) = 3 * (F.filter fun E ↦ E.card ≤ 5).card := by
      rw [← sum_filter, sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
    simpa only [sum_const, Nat.nsmul_eq_mul, sum_add_distrib, hsmall, Nat.mul_comm F.card 6] using hh
  omega

end PaperP1.DisjointSixVertexBudget
