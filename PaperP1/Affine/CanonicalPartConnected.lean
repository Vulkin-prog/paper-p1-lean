module

public import PaperP1.Affine.RelationPartitions
public import PaperP1.Affine.Subfamilies

/-! # Every actual canonical part is connected under restriction

A relation-preserving nontrivial cut of one canonical part would refine
the full canonical partition. Its defining minimality excludes that cut.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalPartConnected

open Finset PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U)

theorem no_cut {C D : Finset ι} (hC : C ∈ (canonicalRelationPartition S).parts)
    (hDC : D ⊆ C) (hD : D.Nonempty) (hrest : (C \ D).Nonempty) :
    ¬(∀ s : (i : ι) → S i, relationAddition S s = 0 → ∑ i ∈ D, (s i).val = 0) := by
  classical
  intro hcut
  let P := canonicalRelationPartition S
  have hdisj : Disjoint D (C \ D) := by
    apply disjoint_left.mpr
    intro i hi hresti
    exact (mem_sdiff.mp hresti).2 hi
  have hcover : D ⊔ (C \ D) = C := by
    ext i
    simp
    exact fun hi ↦ hDC hi
  let Q : Finpartition C := (⊤ : Finpartition D).extend hrest.ne_empty hdisj hcover
  let subparts : ∀ A ∈ P.parts, Finpartition A :=
    fun A _ ↦ if h : A = C then h.symm ▸ Q else ⊤
  let R := P.bind subparts
  have hP : RelationDirectPartition S P := canonicalRelationPartition_respects S
  have hR : RelationDirectPartition S R := by
    intro s hs F hF
    obtain ⟨A, hA, hFA⟩ := Finpartition.mem_bind.mp hF
    by_cases hAC : A = C
    · subst A
      have hFQ : F ∈ Q.parts := by simpa only [subparts, dite_eq_left (Eq.refl C)] using hFA
      change F ∈ insert (C \ D) (⊤ : Finpartition D).parts at hFQ
      rcases mem_insert.mp hFQ with rfl | hFD
      · have hsum := sum_sdiff (f := fun i ↦ (s i).val) hDC
        rw [hcut s hs, add_zero] at hsum
        exact hsum.trans (hP s hs C hC)
      · have hFD' : F = D := mem_singleton.mp (Finpartition.parts_top_subset D hFD)
        rw [hFD']
        exact hcut s hs
    · have hFA' : F ∈ (⊤ : Finpartition A).parts := by
        simpa only [subparts, dite_eq_right hAC] using hFA
      have hFAeq : F = A := mem_singleton.mp (Finpartition.parts_top_subset A hFA')
      rw [hFAeq]
      exact hP s hs A hA
  have hPR : P ≤ R := canonicalRelationPartition_le S R hR
  obtain ⟨F, hFR, hCF⟩ := hPR hC
  obtain ⟨A, hA, hFA⟩ := Finpartition.mem_bind.mp hFR
  have hFAle : F ⊆ A := (subparts A hA).subset hFA
  obtain ⟨i, hiD⟩ := hD
  have hiC := hDC hiD
  have hAC : A = C := (P.eq_of_mem_parts hA hC (hFAle (hCF hiC)) hiC)
  subst A
  have hFQ : F ∈ Q.parts := by simpa only [subparts, dite_eq_left (Eq.refl C)] using hFA
  change F ∈ insert (C \ D) (⊤ : Finpartition D).parts at hFQ
  rcases mem_insert.mp hFQ with rfl | hFD
  · exact (mem_sdiff.mp (hCF hiC)).2 hiD
  · have hFD' : F = D := mem_singleton.mp (Finpartition.parts_top_subset D hFD)
    obtain ⟨j, hj⟩ := hrest
    exact (mem_sdiff.mp hj).2 (hFD' ▸ hCF (mem_sdiff.mp hj).1)

theorem part_connected {C : Finset ι} (hC : C ∈ (canonicalRelationPartition S).parts) :
    canonicalRelationPartition (fun i : C ↦ S i.val) = ⊤ := by
  classical
  let Q := canonicalRelationPartition (fun i : C ↦ S i.val)
  have hQ : RelationDirectPartition (fun i : C ↦ S i.val) Q := canonicalRelationPartition_respects _
  obtain ⟨j, hjC⟩ := (canonicalRelationPartition S).nonempty_of_mem_parts hC
  let jC : C := ⟨j, hjC⟩
  let E := Q.part jC
  have hE : E ∈ Q.parts := Q.part_mem.mpr (mem_univ _)
  have hjE : jC ∈ E := Q.mem_part (mem_univ _)
  by_cases hEtop : E = univ
  · apply top_le_iff.mp
    intro F _
    exact ⟨E, hE, by rw [hEtop]; exact subset_univ _⟩
  · have hproper : ¬(univ : Finset C) ⊆ E := by
      intro h
      exact hEtop (Subset.antisymm (subset_univ _) h)
    obtain ⟨k, _, hk⟩ := not_subset.mp hproper
    let D := E.image (fun i : C ↦ i.val)
    have hDC : D ⊆ C := by
      intro i hi
      obtain ⟨i, _, rfl⟩ := mem_image.mp hi
      exact i.property
    have hD : D.Nonempty := ⟨j, mem_image.mpr ⟨jC, hjE, rfl⟩⟩
    have hkD : k.val ∉ D := by
      intro h
      obtain ⟨i, hi, hik⟩ := mem_image.mp h
      have heq : i = k := Subtype.ext hik
      exact hk (heq ▸ hi)
    have hrest : (C \ D).Nonempty := ⟨k.val, mem_sdiff.mpr ⟨k.property, hkD⟩⟩
    apply False.elim
    apply no_cut S hC hDC hD hrest
    intro s hs
    let r : (i : C) → S i.val := fun i ↦ s i.val
    have hr : relationAddition (fun i : C ↦ S i.val) r = 0 := by
      rw [relationAddition_apply]
      change (∑ i : C, (s i.val).val) = 0
      rw [sum_finset_subtype C (fun i : ι ↦ (s i).val)]
      exact canonicalRelationPartition_respects S s hs C hC
    have hzero := hQ r hr E hE
    calc
      (∑ i ∈ D, (s i).val) = ∑ i ∈ E, (s i.val).val := by
        apply sum_image
        intro i _ k _ hik
        exact Subtype.ext hik
      _ = 0 := hzero

def NoCut : Prop :=
  ∀ D : Finset ι, D.Nonempty → ((univ : Finset ι) \ D).Nonempty →
    ¬(∀ s : (i : ι) → S i, relationAddition S s = 0 → ∑ i ∈ D, (s i).val = 0)

theorem connected_iff_noCut [Nonempty ι] : canonicalRelationPartition S = ⊤ ↔ NoCut S := by
  classical
  constructor
  · intro hconnected D hD hrest
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨C, hC, _⟩ := (canonicalRelationPartition S).exists_mem (mem_univ i)
    have hCtop : C ∈ (⊤ : Finpartition (univ : Finset ι)).parts := by rwa [hconnected] at hC
    have hCeq : C = univ := mem_singleton.mp (Finpartition.parts_top_subset _ hCtop)
    have hUniv : (univ : Finset ι) ∈ (canonicalRelationPartition S).parts := by rwa [hCeq] at hC
    exact no_cut S hUniv (subset_univ D) hD hrest
  · intro hnocut
    let P := canonicalRelationPartition S
    obtain ⟨i⟩ := ‹Nonempty ι›
    let C := P.part i
    have hC : C ∈ P.parts := P.part_mem.mpr (mem_univ _)
    have hCnonempty : C.Nonempty := P.nonempty_of_mem_parts hC
    by_cases hCeq : C = univ
    · apply top_le_iff.mp
      intro F _
      exact ⟨C, hC, by rw [hCeq]; exact subset_univ _⟩
    · have hproper : ¬(univ : Finset ι) ⊆ C := by
        intro h
        exact hCeq (Subset.antisymm (subset_univ _) h)
      obtain ⟨j, hj, hjC⟩ := not_subset.mp hproper
      have hrest : ((univ : Finset ι) \ C).Nonempty := ⟨j, mem_sdiff.mpr ⟨hj, hjC⟩⟩
      exact False.elim (hnocut C hCnonempty hrest (fun s hs ↦ canonicalRelationPartition_respects S s hs C hC))

end PaperP1.CanonicalPartConnected
