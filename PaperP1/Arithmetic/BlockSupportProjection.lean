module

public import PaperP1.Arithmetic.RelativeBlockRelations

/-! # Actual relations with many nonzero block projections reduce to conditional lists -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BlockSupportProjection

open Finset PaperP1.Arithmetic PaperP1.EffectiveExposure

def Relation {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) (s : ℕ) : Prop :=
  ∃ u : Fin r → (ℕ →₀ F₂),
    (∀ i, u i ∈ PaperP1.FiniteEvenSquareClasses.space (blocks i (n i))) ∧
      (∑ i, u i) = 0 ∧ s ≤ (univ.filter fun i ↦ u i ≠ 0).card

def population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (s : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ Relation blocks n s

def codes (r s : ℕ) : Finset (Code r) := by
  classical
  exact univ.filter fun c ↦ s ≤ r - c.1.val

def cell {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (c : Code r) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ Extension c blocks n

theorem mem_population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (s : ℕ) (n : Fin r → ℕ) :
    n ∈ population G blocks s ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ Relation blocks n s := by
  classical
  simp only [population, mem_filter, Fintype.mem_piFinset]

theorem mem_cell {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (c : Code r) (n : Fin r → ℕ) :
    n ∈ cell G blocks c ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ Extension c blocks n := by
  classical
  simp only [cell, mem_filter, Fintype.mem_piFinset]

theorem split_support {r s : ℕ} {V : Type*} [Zero V] [DecidableEq V] (u : Fin r → V) (hs : 0 < s)
    (hsize : s ≤ (univ.filter fun i ↦ u i ≠ 0).card) :
    ∃ c : Code r, s ≤ r - c.1.val ∧
      (∀ i : Fin c.1.val, u (c.2.symm (Sum.inl i)) = 0) ∧
      (∀ i : Fin (r - c.1.val), u (c.2.symm (Sum.inr i)) ≠ 0) := by
  classical
  obtain ⟨i₀, hi₀⟩ := card_pos.mp (hs.trans_le hsize)
  have hne := (mem_filter.mp hi₀).2
  let Z := {i : Fin r // u i = 0}
  let R := {i : Fin r // ¬u i = 0}
  let k := Fintype.card Z
  have hk : k < r := by
    simpa only [Fintype.card_fin, k, Z] using Fintype.card_subtype_lt (p := fun i : Fin r ↦ u i = 0) hne
  let eZ : Fin k ≃ Z := (Fintype.equivFin Z).symm
  have hRcard : Fintype.card R = r - k := by simp only [R, Fintype.card_subtype_compl, Fintype.card_fin, k, Z]
  let eR : Fin (r - k) ≃ R := (Fintype.equivFinOfCardEq hRcard).symm
  let e : Fin r ≃ (Fin k ⊕ Fin (r - k)) :=
    (Equiv.sumCompl (fun i : Fin r ↦ u i = 0)).symm.trans (Equiv.sumCongr eZ.symm eR.symm)
  let c : Code r := ⟨⟨k, hk⟩, e⟩
  have hrightCard : s ≤ r - k := by
    rw [← hRcard]
    simpa only [R, Fintype.card_subtype] using hsize
  refine ⟨c, hrightCard, ?_, ?_⟩
  · intro i
    change u (eZ i).val = 0
    exact (eZ i).property
  · intro i
    change u (eR i).val ≠ 0
    exact (eR i).property

theorem projected_group {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ)
    (s : ℕ) (hs : 0 < s) (hrel : Relation blocks n s) :
    ∃ c ∈ codes r s, Extension c blocks n := by
  classical
  obtain ⟨u, hu, hsum, hsize⟩ := hrel
  obtain ⟨c, hc, _, hright⟩ := split_support u hs hsize
  refine ⟨c, mem_filter.mpr ⟨mem_univ _, hc⟩,
    (fun i ↦ u (c.2.symm (Sum.inr i))), (fun i ↦ ⟨hu _, hright i⟩), ?_⟩
  have hleft : (∑ i : Fin c.1.val, u (c.2.symm (Sum.inl i))) ∈
      PaperP1.OldSpaceProjection.oldSpace (oldValues c blocks (leftCentres c n)) := by
    apply Submodule.sum_mem
    intro i _
    apply PaperP1.ProjectedWindowLists.oldSpace_mono _ (PaperP1.RelativeBlockRelations.effective_le_full _ (hu _))
    intro v hv
    exact mem_biUnion.mpr ⟨i, mem_univ _, hv⟩
  have heq : (∑ i : Fin (r - c.1.val), u (c.2.symm (Sum.inr i))) =
      (∑ i, u i) - ∑ i : Fin c.1.val, u (c.2.symm (Sum.inl i)) := by
    rw [← PaperP1.RelativeBlockRelations.sum_split c u]
    abel
  rw [heq, hsum, zero_sub]
  exact Submodule.neg_mem _ hleft

theorem population_cover {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (s : ℕ) (hs : 0 < s) :
    ∀ n ∈ population G blocks s, ∃ c ∈ codes r s, n ∈ cell G blocks c := by
  intro n hn
  obtain ⟨hnG, hinj, hrel⟩ := (mem_population G blocks s n).mp hn
  obtain ⟨c, hc, hext⟩ := projected_group blocks n s hs hrel
  exact ⟨c, hc, (mem_cell G blocks c n).mpr ⟨hnG, hinj, hext⟩⟩

theorem suffix_effective {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (c : Code r) (n : Fin r → ℕ) (hn : n ∈ cell G blocks c) :
    rightCentres c n ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks (leftCentres c n)) := by
  obtain ⟨hnG, hinj, hext⟩ := (mem_cell G blocks c n).mp hn
  apply (PaperP1.EffectiveWindowLists.mem_lists G _ _ _).mpr
  refine ⟨fun i ↦ hnG _, ?_, hext⟩
  intro i j hij
  exact Sum.inr.inj (c.2.symm.injective (hinj hij))

theorem fibre_count {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ)
    (c : Code r) (p : Fin c.1.val → ℕ) :
    ((cell G blocks c).filter fun n ↦ leftCentres c n = p).card ≤
      (PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)).card := by
  classical
  apply card_le_card_of_injOn (rightCentres c)
  · intro n hn
    obtain ⟨hncell, hnp⟩ := mem_filter.mp hn
    change rightCentres c n ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)
    simpa only [hnp] using suffix_effective G blocks c n hncell
  · intro n hn m hm hnm
    exact determined c n m ((mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm) hnm

theorem cell_count {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (c : Code r) (B : ℝ)
    (hB : ∀ p ∈ Fintype.piFinset (fun _ : Fin c.1.val ↦ G),
      ((PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)).card : ℝ) ≤ B) :
    ((cell G blocks c).card : ℝ) ≤
      ((Fintype.piFinset (fun _ : Fin c.1.val ↦ G)).card : ℝ) * B := by
  classical
  let F := fun p ↦ (cell G blocks c).filter fun n ↦ leftCentres c n = p
  apply PaperP1.FiniteCoverCount.cardinal_le (cell G blocks c) (Fintype.piFinset (fun _ : Fin c.1.val ↦ G)) F B
  · intro n hn
    have hnG := ((mem_cell G blocks c n).mp hn).1
    exact ⟨leftCentres c n, Fintype.mem_piFinset.mpr (fun i ↦ hnG _), mem_filter.mpr ⟨hn, rfl⟩⟩
  · intro p hp
    exact (show ((F p).card : ℝ) ≤
      (PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks p)).card by
        exact_mod_cast fibre_count G blocks c p).trans (hB p hp)

end PaperP1.BlockSupportProjection
