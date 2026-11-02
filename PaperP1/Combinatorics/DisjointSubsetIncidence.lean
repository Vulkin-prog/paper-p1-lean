module

public import PaperP1.Combinatorics.TriplePairIncidence

/-! # Exact incidence between a set with a marked subset and two disjoint sets -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.DisjointSubsetIncidence

open Finset

variable {ι A : Type*} [DecidableEq ι] [AddCommMonoid A]

theorem split_sum (G : Finset ι) (s t : ℕ) (f : Finset ι → Finset ι → A) :
    (∑ I ∈ G.powersetCard (s + t), ∑ D ∈ I.powersetCard s, f D (I \ D)) =
      ∑ D ∈ G.powersetCard s, ∑ E ∈ (G \ D).powersetCard t, f D E := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun v _ ↦ (⟨v.2, v.1 \ v.2⟩ : Σ _ : Finset ι, Finset ι))
  · intro v hv
    obtain ⟨hI, hD⟩ := mem_sigma.mp hv
    obtain ⟨hIG, hIc⟩ := mem_powersetCard.mp hI
    obtain ⟨hDI, hDc⟩ := mem_powersetCard.mp hD
    apply mem_sigma.mpr
    refine ⟨mem_powersetCard.mpr ⟨hDI.trans hIG, hDc⟩, mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro x hx
      obtain ⟨hxI, hxD⟩ := mem_sdiff.mp hx
      exact mem_sdiff.mpr ⟨hIG hxI, hxD⟩
    · change (v.1 \ v.2).card = t
      have hc := card_sdiff_add_card_eq_card hDI
      omega
  · intro v hv w hw heq
    have hDI := (mem_powersetCard.mp (mem_sigma.mp hv).2).1
    have hEW := (mem_powersetCard.mp (mem_sigma.mp hw).2).1
    have hD : v.2 = w.2 := congrArg Sigma.fst heq
    have hE : v.1 \ v.2 = w.1 \ w.2 := congrArg Sigma.snd heq
    have hI : v.1 = w.1 := by
      calc
        _ = v.2 ∪ (v.1 \ v.2) := (union_sdiff_of_subset hDI).symm
        _ = w.2 ∪ (w.1 \ w.2) := by rw [hE, hD]
        _ = _ := union_sdiff_of_subset hEW
    exact Sigma.ext hI (heq_of_eq hD)
  · intro v hv
    obtain ⟨hD, hE⟩ := mem_sigma.mp hv
    obtain ⟨hDG, hDc⟩ := mem_powersetCard.mp hD
    obtain ⟨hEGD, hEc⟩ := mem_powersetCard.mp hE
    have hdis : Disjoint v.1 v.2 := disjoint_left.mpr (fun x hxD hxE ↦ (mem_sdiff.mp (hEGD hxE)).2 hxD)
    have hdiff : (v.1 ∪ v.2) \ v.1 = v.2 := by
      ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hxD | hxE, hxnot⟩
        · exact False.elim (hxnot hxD)
        · exact hxE
      · intro hxE
        exact ⟨Or.inr hxE, fun hxD ↦ disjoint_left.mp hdis hxD hxE⟩
    refine ⟨⟨v.1 ∪ v.2, v.1⟩, mem_sigma.mpr ⟨?_, mem_powersetCard.mpr ⟨subset_union_left, hDc⟩⟩, ?_⟩
    · exact mem_powersetCard.mpr ⟨union_subset hDG (hEGD.trans sdiff_subset), by rw [card_union_of_disjoint hdis, hDc, hEc]⟩
    · exact Sigma.ext rfl (heq_of_eq hdiff)
  · intro v _
    rfl

end PaperP1.DisjointSubsetIncidence
