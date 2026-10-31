module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Card

/-! # Discarding the disjoint supports touched by a finite exceptional set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DiscardTouchedSupports

open Finset

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

def touched (I : Finset ι) (S : ι → Finset V) (H : Finset V) : Finset ι :=
  I.filter fun i ↦ (S i ∩ H).Nonempty

omit [DecidableEq ι] in
theorem touched_subset (I : Finset ι) (S : ι → Finset V) (H : Finset V) :
    touched I S H ⊆ I := filter_subset _ _

theorem remaining_avoids (I : Finset ι) (S : ι → Finset V) (H : Finset V)
    (i : ι) (hi : i ∈ I \ touched I S H) (v : V) (hv : v ∈ S i) : v ∉ H := by
  intro hvH
  obtain ⟨hiI, hiD⟩ := mem_sdiff.mp hi
  exact hiD (mem_filter.mpr ⟨hiI, v, mem_inter.mpr ⟨hv, hvH⟩⟩)

theorem card_touched_le (I : Finset ι) (S : ι → Finset V) (H : Finset V)
    (hdisj : (↑I : Set ι).PairwiseDisjoint S) : (touched I S H).card ≤ H.card := by
  classical
  have hpoint (i : touched I S H) : ∃ v : V, v ∈ S i.val ∧ v ∈ H := by
    obtain ⟨_, v, hv⟩ := mem_filter.mp i.property
    exact ⟨v, (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩
  let f : touched I S H → H := fun i ↦ ⟨(hpoint i).choose, (hpoint i).choose_spec.2⟩
  have hfmem (i : touched I S H) : (f i).val ∈ S i.val := (hpoint i).choose_spec.1
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hiI : i.val ∈ I := (mem_filter.mp i.property).1
    have hjI : j.val ∈ I := (mem_filter.mp j.property).1
    have hpair := hdisj hiI hjI hne
    have heq : (f i).val = (f j).val := congrArg Subtype.val hij
    have hjmem : (f i).val ∈ S j.val := heq ▸ hfmem j
    exact disjoint_left.mp hpair (hfmem i) hjmem
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hc

theorem exists_discard (I : Finset ι) (S : ι → Finset V) (H : Finset V)
    (hdisj : (↑I : Set ι).PairwiseDisjoint S) :
    ∃ D : Finset ι, D ⊆ I ∧ D.card ≤ H.card ∧
      ∀ i ∈ I \ D, ∀ v ∈ S i, v ∉ H := by
  exact ⟨touched I S H, touched_subset I S H, card_touched_le I S H hdisj,
    fun i hi v hv ↦ remaining_avoids I S H i hi v hv⟩

end PaperP1.DiscardTouchedSupports
