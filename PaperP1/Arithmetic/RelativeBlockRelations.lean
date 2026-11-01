module

public import PaperP1.Arithmetic.EffectiveExposure
public import Mathlib.Logic.Equiv.Sum

/-! # Every block participates in an actual relation relative to the old full span

Exposing the support of one such relation leaves the same property for all
remaining blocks, after adjoining the exposed full value blocks.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeBlockRelations

open Finset PaperP1.Arithmetic PaperP1.EffectiveExposure

def Covered {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ) (n : Fin r → ℕ) : Prop :=
  ∀ i, ∃ u : Fin r → (ℕ →₀ F₂),
    (∀ j, u j ∈ PaperP1.FiniteEvenSquareClasses.space (blocks j (n j))) ∧ u i ≠ 0 ∧
      (∑ j, u j) ∈ PaperP1.OldSpaceProjection.oldSpace O

def population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ) :
    Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ Covered blocks O n

def groupValues {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ)
    (q : Fin (r - c.1.val) → ℕ) : Finset ℕ := univ.biUnion fun i ↦ rightBlocks c blocks i (q i)

def GroupRelation {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ) (n : Fin r → ℕ) : Prop :=
  ∃ u : Fin (r - c.1.val) → (ℕ →₀ F₂),
    (∀ i, u i ∈ PaperP1.FiniteEvenSquareClasses.space (rightBlocks c blocks i (rightCentres c n i)) ∧ u i ≠ 0) ∧
      (∑ i, u i) ∈ PaperP1.OldSpaceProjection.oldSpace O

def cell {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ)
    (c : Code r) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧
    GroupRelation c blocks O n ∧ Covered (leftBlocks c blocks) (O ∪ groupValues c blocks (rightCentres c n)) (leftCentres c n)

theorem mem_population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (O : Finset ℕ) (n : Fin r → ℕ) :
    n ∈ population G blocks O ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ Covered blocks O n := by
  classical
  simp only [population, mem_filter, Fintype.mem_piFinset]

theorem mem_cell {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (O : Finset ℕ) (c : Code r) (n : Fin r → ℕ) :
    n ∈ cell G blocks O c ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ GroupRelation c blocks O n ∧
      Covered (leftBlocks c blocks) (O ∪ groupValues c blocks (rightCentres c n)) (leftCentres c n) := by
  classical
  simp only [cell, mem_filter, Fintype.mem_piFinset]

theorem sum_split {r : ℕ} {V : Type*} [AddCommMonoid V] (c : Code r) (u : Fin r → V) :
    (∑ i : Fin c.1.val, u (c.2.symm (Sum.inl i))) +
      (∑ i : Fin (r - c.1.val), u (c.2.symm (Sum.inr i))) = ∑ i, u i := by
  simpa only [Fintype.sum_sum_type] using Equiv.sum_comp c.2.symm u

theorem effective_le_full (S : Finset ℕ) :
    PaperP1.FiniteEvenSquareClasses.space S ≤ PaperP1.OldSpaceProjection.oldSpace S := by
  change PaperP1.FiniteSetValueSpan.evenSpace (K := F₂) parityVec S ≤ PaperP1.FiniteSetValueSpan.span (K := F₂) parityVec S
  exact PaperP1.FiniteSetValueSpan.evenSpace_le_span parityVec S

theorem remainder_covered {r : ℕ} (c : Code r) (blocks : Fin r → ℕ → Finset ℕ)
    (O : Finset ℕ) (n : Fin r → ℕ) (hn : Covered blocks O n) :
    Covered (leftBlocks c blocks) (O ∪ groupValues c blocks (rightCentres c n)) (leftCentres c n) := by
  intro i
  obtain ⟨u, hu, hne, htotal⟩ := hn (c.2.symm (Sum.inl i))
  refine ⟨fun j ↦ u (c.2.symm (Sum.inl j)), (fun j ↦ hu _), hne, ?_⟩
  have htotal' : (∑ j, u j) ∈
      PaperP1.OldSpaceProjection.oldSpace (O ∪ groupValues c blocks (rightCentres c n)) :=
    PaperP1.ProjectedWindowLists.oldSpace_mono subset_union_left htotal
  have hright : (∑ j : Fin (r - c.1.val), u (c.2.symm (Sum.inr j))) ∈
      PaperP1.OldSpaceProjection.oldSpace (O ∪ groupValues c blocks (rightCentres c n)) := by
    apply Submodule.sum_mem
    intro j _
    apply PaperP1.ProjectedWindowLists.oldSpace_mono _ (effective_le_full _ (hu _))
    intro v hv
    exact mem_union_right _ (mem_biUnion.mpr ⟨j, mem_univ _, hv⟩)
  have heq : (∑ j : Fin c.1.val, u (c.2.symm (Sum.inl j))) =
      (∑ j, u j) - ∑ j : Fin (r - c.1.val), u (c.2.symm (Sum.inr j)) := by
    rw [← sum_split c u]
    abel
  rw [heq]
  exact Submodule.sub_mem _ htotal' hright

theorem group_exists {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ)
    (n : Fin r → ℕ) (hr : 0 < r) (hn : Covered blocks O n) :
    ∃ c : Code r, GroupRelation c blocks O n := by
  classical
  let i₀ : Fin r := ⟨0, hr⟩
  obtain ⟨u, hu, hne, htotal⟩ := hn i₀
  let Z := {i : Fin r // u i = 0}
  let R := {i : Fin r // ¬u i = 0}
  let k := Fintype.card Z
  have hk : k < r := by
    simpa only [Fintype.card_fin, k, Z] using Fintype.card_subtype_lt (p := fun i : Fin r ↦ u i = 0) hne
  let eZ : Fin k ≃ Z := (Fintype.equivFin Z).symm
  have hRcard : Fintype.card R = r - k := by
    simp only [R, Fintype.card_subtype_compl, Fintype.card_fin, k, Z]
  let eR : Fin (r - k) ≃ R := (Fintype.equivFinOfCardEq hRcard).symm
  let e : Fin r ≃ (Fin k ⊕ Fin (r - k)) :=
    (Equiv.sumCompl (fun i : Fin r ↦ u i = 0)).symm.trans (Equiv.sumCongr eZ.symm eR.symm)
  let c : Code r := ⟨⟨k, hk⟩, e⟩
  have hleft : ∀ i : Fin c.1.val, u (c.2.symm (Sum.inl i)) = 0 := by
    intro i
    change u (eZ i).val = 0
    exact (eZ i).property
  have hright : ∀ i : Fin (r - c.1.val), u (c.2.symm (Sum.inr i)) ≠ 0 := by
    intro i
    change u (eR i).val ≠ 0
    exact (eR i).property
  refine ⟨c, (fun i ↦ u (c.2.symm (Sum.inr i))), (fun i ↦ ⟨hu _, hright i⟩), ?_⟩
  have hsum := sum_split c u
  rw [sum_eq_zero (fun i _ ↦ hleft i), zero_add] at hsum
  rwa [hsum]

theorem population_cover {r : ℕ} (G : Finset ℕ) (blocks : Fin (r + 1) → ℕ → Finset ℕ) (O : Finset ℕ) :
    ∀ n ∈ population G blocks O, ∃ c ∈ (univ : Finset (Code (r + 1))), n ∈ cell G blocks O c := by
  intro n hn
  obtain ⟨hnG, hinj, hcovered⟩ := (mem_population G blocks O n).mp hn
  obtain ⟨c, hc⟩ := group_exists blocks O n (by omega) hcovered
  exact ⟨c, mem_univ _, (mem_cell G blocks O c n).mpr
    ⟨hnG, hinj, hc, remainder_covered c blocks O n hcovered⟩⟩

theorem group_effective {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ)
    (c : Code r) (n : Fin r → ℕ) (hn : n ∈ cell G blocks O c) :
    rightCentres c n ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) O := by
  obtain ⟨hnG, hinj, hrel, _⟩ := (mem_cell G blocks O c n).mp hn
  apply (PaperP1.EffectiveWindowLists.mem_lists G _ _ _).mpr
  refine ⟨fun i ↦ hnG _, ?_, hrel⟩
  intro i j hij
  exact Sum.inr.inj (c.2.symm.injective (hinj hij))

theorem remainder_population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ)
    (c : Code r) (n : Fin r → ℕ) (hn : n ∈ cell G blocks O c) :
    leftCentres c n ∈ population G (leftBlocks c blocks) (O ∪ groupValues c blocks (rightCentres c n)) := by
  obtain ⟨hnG, hinj, _, hrem⟩ := (mem_cell G blocks O c n).mp hn
  apply (mem_population G _ _ _).mpr
  refine ⟨fun i ↦ hnG _, ?_, hrem⟩
  intro i j hij
  exact Sum.inl.inj (c.2.symm.injective (hinj hij))

theorem fibre_count {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (O : Finset ℕ)
    (c : Code r) (q : Fin (r - c.1.val) → ℕ) :
    ((cell G blocks O c).filter fun n ↦ rightCentres c n = q).card ≤
      (population G (leftBlocks c blocks) (O ∪ groupValues c blocks q)).card := by
  classical
  apply card_le_card_of_injOn (leftCentres c)
  · intro n hn
    obtain ⟨hncell, hnq⟩ := mem_filter.mp hn
    change leftCentres c n ∈ population G (leftBlocks c blocks) (O ∪ groupValues c blocks q)
    simpa only [hnq] using remainder_population G blocks O c n hncell
  · intro n hn m hm hnm
    exact determined c n m hnm ((mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm)

theorem cell_count {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (O : Finset ℕ) (c : Code r) (B : ℝ)
    (hB : ∀ q ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) O,
      ((population G (leftBlocks c blocks) (O ∪ groupValues c blocks q)).card : ℝ) ≤ B) :
    ((cell G blocks O c).card : ℝ) ≤
      ((PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) O).card : ℝ) * B := by
  classical
  let F := fun q ↦ (cell G blocks O c).filter fun n ↦ rightCentres c n = q
  apply PaperP1.FiniteCoverCount.cardinal_le (cell G blocks O c)
    (PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) O) F B
  · intro n hn
    exact ⟨rightCentres c n, group_effective G blocks O c n hn, mem_filter.mpr ⟨hn, rfl⟩⟩
  · intro q hq
    exact (show ((F q).card : ℝ) ≤
      (population G (leftBlocks c blocks) (O ∪ groupValues c blocks q)).card by
        exact_mod_cast fibre_count G blocks O c q).trans (hB q hq)

theorem zero_card (G : Finset ℕ) (blocks : Fin 0 → ℕ → Finset ℕ) (O : Finset ℕ) :
    (population G blocks O).card ≤ 1 := by
  apply card_le_one.mpr
  exact fun n _ m _ ↦ Subsingleton.elim n m

end PaperP1.RelativeBlockRelations
