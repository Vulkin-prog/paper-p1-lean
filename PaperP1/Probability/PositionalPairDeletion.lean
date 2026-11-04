module

public import PaperP1.Probability.PositionalCountProjection
public import Mathlib.Data.Finsupp.Order

/-! # Literal deletion and isolation of active edges in a full counting field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPairDeletion

open Finset PaperP1.PositionalFiniteLaw PaperP1.PositionalCountProjection

variable {ι : Type*}

local instance pairDeletionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def activeEdges (E : Finset (Finset ι)) (v : Configuration ι) : Finset (Finset ι) :=
  E.filter (fun e ↦ ∀ x ∈ e, 0 < v x)

def vertices (E : Finset (Finset ι)) (v : Configuration ι) : Finset ι :=
  (activeEdges E v).biUnion id

def edgeVector (e : Finset ι) : Configuration ι := ∑ x ∈ e, direction x

def deleteEdge (e : Finset ι) (v : Configuration ι) : Configuration ι := v - edgeVector e

def isolate (E : Finset (Finset ι)) (v : Configuration ι) : Configuration ι :=
  v.filter (fun x ↦ x ∉ vertices E v)

theorem totalCount_mono {u v : Configuration ι} (h : ∀ x, u x ≤ v x) :
    totalCount u ≤ totalCount v := by
  have huv : u ≤ v := h
  obtain ⟨w, hw⟩ := exists_add_of_le huv
  rw [hw, map_add]
  exact Nat.le_add_right _ _

@[simp] theorem edgeVector_apply (e : Finset ι) (x : ι) :
    edgeVector e x = if x ∈ e then 1 else 0 := by
  classical
  simp [edgeVector, Finset.sum_apply', direction, Finsupp.single_apply]

@[simp] theorem totalCount_edgeVector (e : Finset ι) : totalCount (edgeVector e) = e.card := by
  simp [edgeVector]

theorem deleteEdge_le (e : Finset ι) (v : Configuration ι) (x : ι) :
    deleteEdge e v x ≤ v x := by
  rw [deleteEdge, Finsupp.tsub_apply]
  exact Nat.sub_le _ _

theorem totalCount_deleteEdge_le (e : Finset ι) (v : Configuration ι) :
    totalCount (deleteEdge e v) ≤ totalCount v := totalCount_mono (deleteEdge_le e v)

theorem edgeVector_le_of_active (E : Finset (Finset ι)) (v : Configuration ι)
    {e : Finset ι} (he : e ∈ activeEdges E v) : edgeVector e ≤ v := by
  intro x
  rw [edgeVector_apply]
  by_cases hx : x ∈ e
  · rw [ite_eq_left hx]
    exact Nat.succ_le_of_lt ((mem_filter.mp he).2 x hx)
  · rw [ite_eq_right hx]
    exact Nat.zero_le _

theorem deleteEdge_add (E : Finset (Finset ι)) (v : Configuration ι)
    {e : Finset ι} (he : e ∈ activeEdges E v) : deleteEdge e v + edgeVector e = v :=
  tsub_add_cancel_of_le (edgeVector_le_of_active E v he)

theorem totalCount_deleteEdge_add (E : Finset (Finset ι)) (v : Configuration ι)
    {e : Finset ι} (he : e ∈ activeEdges E v) :
    totalCount (deleteEdge e v) + e.card = totalCount v := by
  have hh := congrArg totalCount (deleteEdge_add E v he)
  simpa only [map_add, totalCount_edgeVector] using hh

theorem totalCount_deletePair (E : Finset (Finset ι)) (v : Configuration ι)
    {e : Finset ι} (he : e ∈ activeEdges E v) (hcard : e.card = 2) :
    totalCount (deleteEdge e v) = totalCount v - 2 := by
  have hh := totalCount_deleteEdge_add E v he
  rw [hcard] at hh
  omega

theorem isolate_le (E : Finset (Finset ι)) (v : Configuration ι) (x : ι) :
    isolate E v x ≤ v x := by
  rw [isolate, Finsupp.filter_apply]
  split_ifs <;> omega

theorem totalCount_isolate_le (E : Finset (Finset ι)) (v : Configuration ι) :
    totalCount (isolate E v) ≤ totalCount v := totalCount_mono (isolate_le E v)

theorem isolate_eq_self_of_no_active (E : Finset (Finset ι)) (v : Configuration ι)
    (h : activeEdges E v = ∅) : isolate E v = v := by
  ext x
  simp only [isolate, Finsupp.filter_apply, vertices, h, biUnion_empty, notMem_empty,
    not_false_eq_true, ite_true]

theorem isolate_no_active (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e.Nonempty) : activeEdges E (isolate E v) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heE, heactive⟩ := mem_filter.mp he
  have heold : e ∈ activeEdges E v := mem_filter.mpr ⟨heE, fun x hx ↦
    (heactive x hx).trans_le (isolate_le E v x)⟩
  obtain ⟨x, hx⟩ := hE e heE
  have hxvertices : x ∈ vertices E v := mem_biUnion.mpr ⟨e, heold, hx⟩
  have hxzero : isolate E v x = 0 := by simp only [isolate, Finsupp.filter_apply,
    hxvertices, not_true_eq_false, ite_false]
  have hh := heactive x hx
  rw [hxzero] at hh
  omega

theorem vertices_positive (E : Finset (Finset ι)) (v : Configuration ι)
    {x : ι} (hx : x ∈ vertices E v) : 0 < v x := by
  obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
  exact (mem_filter.mp he).2 x hxe

theorem vertices_card_upper (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e.card = 2) : (vertices E v).card ≤ 2 * (activeEdges E v).card := by
  classical
  calc
    _ ≤ ∑ e ∈ activeEdges E v, e.card := card_biUnion_le
    _ = ∑ _e ∈ activeEdges E v, 2 := sum_congr rfl
      (fun e he ↦ hE e (mem_filter.mp he).1)
    _ = _ := by simp [Nat.mul_comm]

theorem vertices_card_lower (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e.card = 2) (hne : (activeEdges E v).Nonempty) :
    2 ≤ (vertices E v).card := by
  classical
  obtain ⟨e, he⟩ := hne
  have hsub : e ⊆ vertices E v := fun x hx ↦ mem_biUnion.mpr ⟨e, he, hx⟩
  simpa only [hE e (mem_filter.mp he).1] using card_le_card hsub

theorem isolate_binary_add (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) : isolate E v + edgeVector (vertices E v) = v := by
  ext x
  rw [Finsupp.add_apply, isolate, Finsupp.filter_apply, edgeVector_apply]
  by_cases hx : x ∈ vertices E v
  · rw [ite_eq_right (not_not.mpr hx), ite_eq_left hx, zero_add]
    have hpos := vertices_positive E v hx
    have hcap := hv x
    omega
  · rw [ite_eq_left hx, ite_eq_right hx, add_zero]

theorem totalCount_isolate_binary_add (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) :
    totalCount (isolate E v) + (vertices E v).card = totalCount v := by
  have hh := congrArg totalCount (isolate_binary_add E v hv)
  simpa only [map_add, totalCount_edgeVector] using hh

def oneCount (E : Finset (Finset ι)) (v : Configuration ι) : ℕ :=
  totalCount v - if (activeEdges E v).Nonempty then 2 else 0

theorem one_all_count_cost (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hE : ∀ e ∈ E, e.card = 2) :
    totalCount (isolate E v) ≤ oneCount E v ∧
      oneCount E v - totalCount (isolate E v) ≤
        (activeEdges E v).card * ((activeEdges E v).card - 1) := by
  by_cases hne : (activeEdges E v).Nonempty
  · have hlo := vertices_card_lower E v hE hne
    have hup := vertices_card_upper E v hE
    have heq := totalCount_isolate_binary_add E v hv
    have hk : 1 ≤ (activeEdges E v).card := card_pos.mpr hne
    rw [oneCount, ite_eq_left hne]
    constructor
    · omega
    · by_cases hk1 : (activeEdges E v).card = 1
      · rw [hk1] at hup
        simp only [hk1, Nat.sub_self, mul_zero]
        omega
      · have hk2 : 2 ≤ (activeEdges E v).card := by omega
        have hfirst : totalCount v - 2 - totalCount (isolate E v) ≤
            2 * ((activeEdges E v).card - 1) := by omega
        have hmul : 2 * ((activeEdges E v).card - 1) ≤
            (activeEdges E v).card * ((activeEdges E v).card - 1) :=
          Nat.mul_le_mul_right _ hk2
        exact hfirst.trans hmul
  · have hempty := not_nonempty_iff_eq_empty.mp hne
    rw [oneCount, ite_eq_right hne, Nat.sub_zero, isolate_eq_self_of_no_active E v hempty]
    exact ⟨le_rfl, by simp only [Nat.sub_self]; exact Nat.zero_le _⟩

end PaperP1.PositionalPairDeletion
