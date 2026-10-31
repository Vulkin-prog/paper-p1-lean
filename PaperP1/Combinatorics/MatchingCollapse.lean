module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Lean.Elab.Tactic.Omega

/-! # Counting the image after disjoint pair collisions and one zero -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MatchingCollapse

open Finset

variable {U W : Type*} [DecidableEq U] [DecidableEq W] [Zero W]

def choosePoint (default : U) (A : Finset U) : U :=
  if h : A.Nonempty then h.choose else default

omit [DecidableEq U] in
theorem choosePoint_mem (default : U) {A : Finset U} (hA : A.Nonempty) :
    choosePoint default A ∈ A := by
  simp only [choosePoint, dite_eq_left hA]
  exact hA.choose_spec

/-- Every disjoint identified pair costs one image point; a specified zero
costs one more. No assertion that these are all collisions is needed. -/
theorem image_erase_zero_card_bound (S : Finset U) (E : Finset (Finset U)) (α : U) (f : U → W)
    (hα : α ∈ S) (hzero : f α = 0)
    (hpair : ∀ A ∈ E, A ⊆ S ∧ A.card = 2 ∧ α ∉ A)
    (hdisjoint : ∀ A ∈ E, ∀ B ∈ E, A ≠ B → Disjoint A B)
    (hconstant : ∀ A ∈ E, ∀ a ∈ A, ∀ b ∈ A, f a = f b) :
    ((S.image f).erase 0).card + E.card + 1 ≤ S.card := by
  let R := E.image (choosePoint α)
  let H := insert α R
  have hnonempty (A : Finset U) (hA : A ∈ E) : A.Nonempty := by
    apply card_pos.mp
    rw [(hpair A hA).2.1]
    decide
  have hchosen (A : Finset U) (hA : A ∈ E) : choosePoint α A ∈ A :=
    choosePoint_mem α (hnonempty A hA)
  have hinj : Set.InjOn (choosePoint α) (↑E : Set (Finset U)) := by
    intro A hA B hB heq
    by_contra hne
    have h := disjoint_left.mp (hdisjoint A hA B hB hne) (hchosen A hA)
    exact h (heq.symm ▸ hchosen B hB)
  have hcardR : R.card = E.card := card_image_iff.mpr hinj
  have hαR : α ∉ R := by
    intro h
    obtain ⟨A, hA, heq⟩ := mem_image.mp h
    exact (hpair A hA).2.2 (heq ▸ hchosen A hA)
  have hcardH : H.card = E.card + 1 := by rw [card_insert_of_notMem hαR, hcardR]
  have hHS : H ⊆ S := by
    intro a ha
    obtain rfl | ha := mem_insert.mp ha
    · exact hα
    · obtain ⟨A, hA, rfl⟩ := mem_image.mp ha
      exact (hpair A hA).1 (hchosen A hA)
  have hcover : (S.image f).erase 0 ⊆ (S \ H).image f := by
    intro y hy
    obtain ⟨hy0, hyS⟩ := mem_erase.mp hy
    obtain ⟨a, haS, hay⟩ := mem_image.mp hyS
    by_cases haH : a ∈ H
    · have haα : a ≠ α := by
        intro heq
        subst a
        exact hy0 (hay.symm.trans hzero)
      have haR : a ∈ R := (mem_insert.mp haH).resolve_left haα
      obtain ⟨A, hA, hchosenA⟩ := mem_image.mp haR
      obtain ⟨x, b, hxb, hAb⟩ := card_eq_two.mp (hpair A hA).2.1
      have haA : a ∈ A := hchosenA ▸ hchosen A hA
      have hb : ∃ b, b ∈ A ∧ b ≠ a := by
        rw [hAb] at haA ⊢
        simp only [mem_insert, mem_singleton] at haA
        rcases haA with rfl | rfl
        · exact ⟨b, by simp, hxb.symm⟩
        · exact ⟨x, by simp, hxb⟩
      obtain ⟨b, hbA, hba⟩ := hb
      have hbR : b ∉ R := by
        intro hbR
        obtain ⟨B, hB, hchosenB⟩ := mem_image.mp hbR
        by_cases hAB : A = B
        · subst B
          exact hba (hchosenB.symm.trans hchosenA)
        · exact disjoint_left.mp (hdisjoint A hA B hB hAB) hbA (hchosenB ▸ hchosen B hB)
      have hbH : b ∉ H := by
        simp only [H, mem_insert, not_or]
        exact ⟨fun h ↦ (hpair A hA).2.2 (h ▸ hbA), hbR⟩
      apply mem_image.mpr
      refine ⟨b, mem_sdiff.mpr ⟨(hpair A hA).1 hbA, hbH⟩, ?_⟩
      exact (hconstant A hA a (hchosenA ▸ hchosen A hA) b hbA).symm.trans hay
    · exact mem_image.mpr ⟨a, mem_sdiff.mpr ⟨haS, haH⟩, hay⟩
  have himage : ((S.image f).erase 0).card ≤ (S \ H).card :=
    (card_le_card hcover).trans (card_image_le)
  have hsum := card_sdiff_add_card_eq_card hHS
  omega

end PaperP1.MatchingCollapse
