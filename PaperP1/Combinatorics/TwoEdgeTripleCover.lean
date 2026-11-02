module

public import Mathlib.Data.Finset.Powerset
public import Lean.Elab.Tactic.Omega

/-! # The third vertex and the other edge inside an actual three-element family -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.TwoEdgeTripleCover

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem third_vertex {T e : Finset ι} (hT : T.card = 3) (he : e.card = 2) (hesub : e ⊆ T) :
    ∃ z : ι, z ∈ T ∧ z ∉ e ∧ T = e ∪ {z} := by
  have hdiff : (T \ e).card = 1 := by rw [card_sdiff_of_subset hesub, hT, he]
  obtain ⟨z, hz⟩ := card_eq_one.mp hdiff
  have hzmem : z ∈ T \ e := by rw [hz]; simp
  exact ⟨z, (mem_sdiff.mp hzmem).1, (mem_sdiff.mp hzmem).2,
    by have hh := union_sdiff_of_subset hesub; rw [hz] at hh; exact hh.symm⟩

theorem other_edge {T e f : Finset ι} {z : ι} (he : e.card = 2) (hf : f.card = 2)
    (hfT : f ⊆ T) (hef : e ≠ f) (hT : T = e ∪ {z}) :
    ∃ u ∈ e, f = {u, z} ∧ u ≠ z := by
  have hzf : z ∈ f := by
    by_contra hn
    have hfe : f ⊆ e := by
      intro u hu
      have huT := hfT hu
      rw [hT] at huT
      rcases mem_union.mp huT with hue | huz
      · exact hue
      · exact False.elim (hn ((mem_singleton.mp huz) ▸ hu))
    exact hef ((eq_of_subset_of_card_le hfe (by omega)).symm)
  have hdiff : (f.erase z).card = 1 := by have hh := card_erase_add_one hzf; omega
  obtain ⟨u, hu⟩ := card_eq_one.mp hdiff
  have humem : u ∈ f.erase z := by rw [hu]; simp
  have hune : u ≠ z := (mem_erase.mp humem).1
  have huf : u ∈ f := (mem_erase.mp humem).2
  have hue : u ∈ e := by
    have huT := hfT huf
    rw [hT] at huT
    exact (mem_union.mp huT).resolve_right (by simpa only [mem_singleton] using hune)
  refine ⟨u, hue, ?_, hune⟩
  calc
    f = insert z (f.erase z) := (insert_erase hzf).symm
    _ = {z, u} := by rw [hu]
    _ = {u, z} := pair_comm _ _

theorem union_card_three {e f : Finset ι} (he : e.card = 2) (hf : f.card = 2)
    (hef : e ≠ f) (hnd : ¬Disjoint e f) : (e ∪ f).card = 3 := by
  have hIpos : 1 ≤ (e ∩ f).card := by
    obtain ⟨z, hze, hzf⟩ := not_disjoint_iff.mp hnd
    exact card_pos.mpr ⟨z, mem_inter.mpr ⟨hze, hzf⟩⟩
  have hIlt : (e ∩ f).card < 2 := by
    by_contra hh
    have heq : e ∩ f = e := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hefsub : e ⊆ f := by rw [← heq]; exact inter_subset_right
    exact hef (eq_of_subset_of_card_le hefsub (by omega))
  have hcount := card_union_add_card_inter e f
  omega

end PaperP1.TwoEdgeTripleCover
