module

public import PaperP1.Algebra.CoordinateRestrictionRank
public import PaperP1.Combinatorics.PinnedGraphResolution
public import Mathlib.Algebra.Field.ZMod

/-! # Covering ternary binary constraints leaves an actual pinned graph -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoverGraphResolution

open Finset PaperP1.Arithmetic PaperP1.CoordinateRestrictionRank PaperP1.PinnedGraphResolution

variable {V ι : Type*} [Fintype V] [DecidableEq V]

local instance coverGraphPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def rowSolutions (rows : ι → Finset V) : Submodule F₂ (V → F₂) where
  carrier := {f | ∀ i, (∑ v ∈ rows i, f v) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i
    simp only [Pi.add_apply, sum_add_distrib, hf i, hg i, add_zero]
  smul_mem' := by
    intro a f hf i
    simp only [Pi.smul_apply, ← smul_sum, hf i, smul_zero]

def IsCover (rows : ι → Finset V) (D : Finset V) : Prop :=
  ∀ i, 3 ≤ (rows i).card → (rows i ∩ D).Nonempty

def pruned (rows : ι → Finset V) (D : Finset V) (i : ι) : Finset V := rows i \ D

omit [Fintype V] in
theorem pruned_card_le_two {rows : ι → Finset V} (hrows : ∀ i, (rows i).card ≤ 3)
    {D : Finset V} (hD : IsCover rows D) (i : ι) : (pruned rows D i).card ≤ 2 := by
  have hsplit := card_sdiff_add_card_inter (rows i) D
  have hbound := hrows i
  by_cases hthree : 3 ≤ (rows i).card
  · have hnonempty := (hD i hthree).card_pos
    unfold pruned
    omega
  · have hle := card_le_card (sdiff_subset : rows i \ D ⊆ rows i)
    unfold pruned
    omega

def graph (rows : ι → Finset V) (D : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i, pruned rows D i = {u, v}
  symm := ⟨fun _ _ h ↦ by obtain ⟨hne, i, hi⟩ := h; exact ⟨hne.symm, i, by simpa only [pair_comm] using hi⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

def pins (rows : ι → Finset V) (D : Finset V) : Finset V := by
  classical
  exact D ∪ univ.filter (fun v ↦ ∃ i, pruned rows D i = {v})

omit [Fintype V] in
theorem sum_pruned {rows : ι → Finset V} {D : Finset V} {f : V → F₂}
    (hf : ∀ v ∈ D, f v = 0) (i : ι) : (∑ v ∈ pruned rows D i, f v) = ∑ v ∈ rows i, f v := by
  apply sum_subset sdiff_subset
  intro v hv hnot
  have hvD : v ∈ D := by
    by_contra h
    exact hnot (mem_sdiff.mpr ⟨hv, h⟩)
  exact hf v hvD

theorem zeroed_mem_graph {rows : ι → Finset V} {D : Finset V} {f : V → F₂}
    (hf : f ∈ zeroed (rowSolutions rows) D) : f ∈ PinnedGraphSpace (graph rows D) (pins rows D) := by
  classical
  refine ⟨?_, ?_⟩
  · intro u v huv
    obtain ⟨hne, i, hi⟩ := huv
    have hrow := hf.1 i
    rw [← sum_pruned hf.2 i, hi, sum_pair hne] at hrow
    exact (eq_neg_of_add_eq_zero_left hrow).trans (ZMod.neg_eq_self_mod_two (f v))
  · intro v hv
    obtain hv | hv := mem_union.mp hv
    · exact hf.2 v hv
    · obtain ⟨i, hi⟩ := (mem_filter.mp hv).2
      have hrow := hf.1 i
      rw [← sum_pruned hf.2 i, hi, sum_singleton] at hrow
      exact hrow

theorem graph_mem_zeroed {rows : ι → Finset V} (hrows : ∀ i, (rows i).card ≤ 3)
    {D : Finset V} (hD : IsCover rows D) {f : V → F₂}
    (hf : f ∈ PinnedGraphSpace (graph rows D) (pins rows D)) : f ∈ zeroed (rowSolutions rows) D := by
  classical
  have hfD : ∀ v ∈ D, f v = 0 := fun v hv ↦ hf.2 v (mem_union_left _ hv)
  refine ⟨?_, hfD⟩
  intro i
  rw [← sum_pruned hfD i]
  have hbound := pruned_card_le_two hrows hD i
  have hcases : (pruned rows D i).card = 0 ∨ (pruned rows D i).card = 1 ∨ (pruned rows D i).card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · rw [card_eq_zero.mp hzero, sum_empty]
  · obtain ⟨v, hv⟩ := card_eq_one.mp hone
    rw [hv, sum_singleton]
    exact hf.2 v (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, i, hv⟩))
  · obtain ⟨u, v, hne, huv⟩ := card_eq_two.mp htwo
    rw [huv, sum_pair hne, hf.1 (show (graph rows D).Adj u v from ⟨hne, i, huv⟩)]
    exact ZModModule.add_self (f v)

theorem zeroed_eq_graph_space {rows : ι → Finset V} (hrows : ∀ i, (rows i).card ≤ 3)
    {D : Finset V} (hD : IsCover rows D) :
    zeroed (rowSolutions rows) D = PinnedGraphSpace (graph rows D) (pins rows D) := by
  ext f
  exact ⟨zeroed_mem_graph, graph_mem_zeroed hrows hD⟩

omit [Fintype V] [DecidableEq V] in
theorem zeroed_mono {R S : Submodule F₂ (V → F₂)} (hRS : R ≤ S) (D : Finset V) : zeroed R D ≤ zeroed S D :=
  fun _ hf ↦ ⟨hRS hf.1, hf.2⟩

theorem residual_rank_bound {rows : ι → Finset V} (hrows : ∀ i, (rows i).card ≤ 3)
    {D : Finset V} (hD : IsCover rows D) (R : Submodule F₂ (V → F₂)) (hR : R ≤ rowSolutions rows) :
    Module.finrank F₂ (zeroed R D) ≤ Fintype.card (UnpinnedComponent (graph rows D) (pins rows D)) := by
  classical
  have hle := Submodule.finrank_mono (zeroed_mono hR D)
  rw [zeroed_eq_graph_space hrows hD, finrank_pinnedGraphSpace] at hle
  exact hle

end PaperP1.CoverGraphResolution
