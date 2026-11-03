module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

/-! # Zero and repeated coordinates cost at most twice the loss of distinct nonzero images -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ImageRepetitionBudget

open Finset

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Zero β] [DecidableEq β]

def good (f : ι → β) : Finset ι := by
  classical
  exact univ.filter fun i ↦ f i ≠ 0 ∧ ∀ j, f j = f i → j = i

def bad (f : ι → β) : Finset ι := univ \ good f

theorem mem_good (f : ι → β) (i : ι) :
    i ∈ good f ↔ f i ≠ 0 ∧ ∀ j, f j = f i → j = i := by
  classical
  simp only [good, mem_filter, mem_univ, true_and]

theorem good_injective (f : ι → β) : Set.InjOn f (good f : Set ι) := by
  intro i hi j hj heq
  exact ((mem_good f i).mp hi).2 j heq.symm |>.symm

theorem bad_budget (f : ι → β) :
    (bad f).card + 2 * ((univ.image f).erase 0).card ≤ 2 * Fintype.card ι := by
  classical
  let labels := (univ.image f).erase 0
  let L := labels \ (good f).image f
  let fibre (α : β) := univ.filter fun i ↦ f i = α
  have htwo (α : β) (hα : α ∈ L) : 2 ≤ (fibre α).card := by
    obtain ⟨hαlabels, hαgood⟩ := mem_sdiff.mp hα
    obtain ⟨hα0, hαimage⟩ := mem_erase.mp hαlabels
    obtain ⟨i, _, hi⟩ := mem_image.mp hαimage
    have hni : i ∉ good f := fun h ↦ hαgood (mem_image.mpr ⟨i, h, hi⟩)
    have hnot : ¬∀ j, f j = f i → j = i := by
      intro hall
      apply hni
      exact (mem_good f i).mpr ⟨by rw [hi]; exact hα0, hall⟩
    push Not at hnot
    obtain ⟨j, hj, hne⟩ := hnot
    have hii : i ∈ fibre α := mem_filter.mpr ⟨mem_univ _, hi⟩
    have hjj : j ∈ fibre α := mem_filter.mpr ⟨mem_univ _, hj.trans hi⟩
    exact Finset.one_lt_card.mpr ⟨i, hii, j, hjj, hne.symm⟩
  have hdisj : (L : Set β).PairwiseDisjoint fibre := by
    intro α hα δ hδ hne
    apply Finset.disjoint_left.mpr
    intro i hi hδi
    exact hne ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hδi).2)
  have hsubset : L.biUnion fibre ⊆ bad f := by
    intro i hi
    obtain ⟨α, hα, hif⟩ := mem_biUnion.mp hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hig
    exact (mem_sdiff.mp hα).2 (mem_image.mpr ⟨i, hig, (mem_filter.mp hif).2⟩)
  have hL : 2 * L.card ≤ (bad f).card := by
    calc
      2 * L.card = ∑ _α ∈ L, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ α ∈ L, (fibre α).card := Finset.sum_le_sum htwo
      _ = (L.biUnion fibre).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (bad f).card := Finset.card_le_card hsubset
  have himage : ((good f).image f).card = (good f).card := card_image_of_injOn (good_injective f)
  have hcover : labels.card ≤ L.card + ((good f).image f).card := card_le_card_sdiff_add_card
  rw [himage] at hcover
  have hpartition : (bad f).card + (good f).card = Fintype.card ι := by
    simpa only [bad, card_univ] using card_sdiff_add_card_eq_card (subset_univ (good f))
  change (bad f).card + 2 * labels.card ≤ 2 * Fintype.card ι
  omega

end PaperP1.ImageRepetitionBudget
