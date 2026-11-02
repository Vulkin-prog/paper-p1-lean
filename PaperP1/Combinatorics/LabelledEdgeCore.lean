module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-! # Actual finite labelled-edge pruning with an explicit density threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LabelledEdgeCore

open Finset

variable {V E : Type*}

local instance : DecidableEq V := Classical.decEq _
local instance : DecidableEq E := Classical.decEq _

def inside (left right : E → V) (S : Finset E) (U : Finset V) : Finset E :=
  S.filter (fun e ↦ left e ∈ U ∧ right e ∈ U)

def incident (left right : E → V) (S : Finset E) (v : V) : Finset E :=
  S.filter (fun e ↦ left e = v ∨ right e = v)

def touching (left right : E → V) (S : Finset E) (U : Finset V) : Finset E :=
  S.filter (fun e ↦ left e ∈ U ∨ right e ∈ U)

theorem mem_inside (left right : E → V) (S : Finset E) (U : Finset V) (e : E) :
    e ∈ inside left right S U ↔ e ∈ S ∧ left e ∈ U ∧ right e ∈ U := mem_filter

theorem mem_incident (left right : E → V) (S : Finset E) (v : V) (e : E) :
    e ∈ incident left right S v ↔ e ∈ S ∧ (left e = v ∨ right e = v) := mem_filter

theorem mem_touching (left right : E → V) (S : Finset E) (U : Finset V) (e : E) :
    e ∈ touching left right S U ↔ e ∈ S ∧ (left e ∈ U ∨ right e ∈ U) := mem_filter

theorem incident_sum_swap (left right : E → V) (S : Finset E) (U : Finset V) :
    ∑ v ∈ U, (incident left right S v).card =
      ∑ e ∈ S, (U.filter (fun v ↦ left e = v ∨ right e = v)).card := by
  simp only [incident, card_eq_sum_ones, sum_filter]
  rw [sum_comm]

theorem incident_sum_le (left right : E → V) (S : Finset E) (U : Finset V) :
    ∑ v ∈ U, (incident left right S v).card ≤ 2 * (touching left right S U).card := by
  rw [incident_sum_swap]
  have hbound (e : E) :
      (U.filter (fun v ↦ left e = v ∨ right e = v)).card ≤
        if left e ∈ U ∨ right e ∈ U then 2 else 0 := by
    by_cases h : left e ∈ U ∨ right e ∈ U
    · rw [ite_eq_left h]
      have hs : U.filter (fun v ↦ left e = v ∨ right e = v) ⊆ {left e, right e} := by
        intro v hv
        rcases (mem_filter.mp hv).2 with hl | hr
        · simp [hl]
        · simp [hr]
      exact (card_le_card hs).trans card_le_two
    · rw [ite_eq_right h]
      have he : U.filter (fun v ↦ left e = v ∨ right e = v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hvU, hl | hr⟩ := mem_filter.mp hv
        · exact h (Or.inl (hl.symm ▸ hvU))
        · exact h (Or.inr (hr.symm ▸ hvU))
      simp [he]
  calc
    ∑ e ∈ S, (U.filter (fun v ↦ left e = v ∨ right e = v)).card ≤
        ∑ e ∈ S, if left e ∈ U ∨ right e ∈ U then 2 else 0 := sum_le_sum (fun e _ ↦ hbound e)
    _ = 2 * (touching left right S U).card := by
      simp [touching, ← sum_filter, Nat.mul_comm]

theorem inside_subset (left right : E → V) (S : Finset E) (U : Finset V) :
    inside left right S U ⊆ S := filter_subset _ _

theorem incident_subset (left right : E → V) (S : Finset E) (v : V) :
    incident left right S v ⊆ S := filter_subset _ _

theorem inside_mono (left right : E → V) (S : Finset E) {U W : Finset V} (h : U ⊆ W) :
    inside left right S U ⊆ inside left right S W := by
  intro e he
  obtain ⟨heS, hel, her⟩ := (mem_inside left right S U e).mp he
  exact (mem_inside left right S W e).mpr ⟨heS, h hel, h her⟩

theorem inside_erase (left right : E → V) (S : Finset E) (U : Finset V) (v : V) :
    inside left right S (U.erase v) =
      inside left right S U \ incident left right (inside left right S U) v := by
  apply Finset.ext
  intro e
  simp only [mem_inside, mem_erase, mem_sdiff, mem_incident]
  tauto

theorem erase_card_budget (left right : E → V) (S : Finset E) (U : Finset V) (v : V) :
    (inside left right S (U.erase v)).card +
      (incident left right (inside left right S U) v).card = (inside left right S U).card := by
  rw [inside_erase]
  exact card_sdiff_add_card_eq_card (incident_subset left right (inside left right S U) v)

theorem dense_core (left right : E → V) (S : Finset E) (U : Finset V) (t : ℕ)
    (hdense : t * U.card < (inside left right S U).card) :
    ∃ W ⊆ U, W.Nonempty ∧ (inside left right S W).Nonempty ∧
      ∀ v ∈ W, t ≤ (incident left right (inside left right S W) v).card := by
  revert hdense
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro hdense
    by_cases hlow : ∃ v ∈ U, (incident left right (inside left right S U) v).card < t
    · obtain ⟨v, hv, hdegree⟩ := hlow
      have hcard := card_erase_add_one hv
      have hbudget := erase_card_budget left right S U v
      have hnext : t * (U.erase v).card < (inside left right S (U.erase v)).card := by
        rw [← hcard, Nat.mul_add, Nat.mul_one] at hdense
        omega
      obtain ⟨W, hWU, hW, hE, hmin⟩ := ih (U.erase v) (erase_ssubset hv) hnext
      exact ⟨W, hWU.trans (erase_subset _ _), hW, hE, hmin⟩
    · have hE : (inside left right S U).Nonempty := card_pos.mp (by omega)
      obtain ⟨e, he⟩ := hE
      have hU : U.Nonempty := ⟨left e, ((mem_inside left right S U e).mp he).2.1⟩
      refine ⟨U, subset_refl U, hU, ⟨e, he⟩, ?_⟩
      intro v hv
      by_contra h
      exact hlow ⟨v, hv, by omega⟩

theorem finite_dense_core [Fintype V] (left right : E → V) (S : Finset E) (t : ℕ)
    (hdense : t * Fintype.card V < S.card) :
    ∃ W : Finset V, W.Nonempty ∧ (inside left right S W).Nonempty ∧
      ∀ v ∈ W, t ≤ (incident left right (inside left right S W) v).card := by
  have heq : inside left right S univ = S := by
    simp [inside]
  obtain ⟨W, _hW, hnonempty, he, hmin⟩ := dense_core left right S univ t (by simpa [heq] using hdense)
  exact ⟨W, hnonempty, he, hmin⟩

end PaperP1.LabelledEdgeCore
