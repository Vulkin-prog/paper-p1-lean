module

public import PaperP1.Arithmetic.SmoothMotifReindex
public import PaperP1.Combinatorics.TransverseMotifSelection
public import Mathlib.Data.Fintype.Perm

/-! # A fixed population of small transverse motifs has a common linear block

Every positive three-block type of total size at most five has a singleton.
There are only twenty-four permutation/left-degree choices; no cover or
component ordering is enumerated.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallTransverseSelection

open Finset PaperP1.TransverseMotifs PaperP1.SmoothMotifReindex

abbrev TypeChoice := Equiv.Perm (Fin 3) × Fin 4

def Fits {L : ℕ} (t : TypeChoice) (E : Finset (Vertex L)) : Prop :=
  0 < t.2.val ∧ (offsets (reindex t.1 E) 0).card = t.2.val ∧
    (offsets (reindex t.1 E) 1).card = 1

theorem singleton_block {L : ℕ} (E : Finset (Vertex L)) (hE : Transverse E) (hsize : E.card ≤ 5) :
    ∃ i : Fin 3, (offsets E i).card = 1 := by
  by_contra h
  have hn : ∀ i : Fin 3, (offsets E i).card ≠ 1 := by simpa only [not_exists] using h
  have h0 := (hE 0).card_pos
  have h1 := (hE 1).card_pos
  have h2 := (hE 2).card_pos
  have hc := card_decomposition E
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  omega

theorem exists_type {L : ℕ} (E : Finset (Vertex L)) (hE : Transverse E) (hsize : E.card ≤ 5) :
    ∃ t : TypeChoice, Fits t E := by
  classical
  obtain ⟨i, hi⟩ := singleton_block E hE hsize
  let e : Equiv.Perm (Fin 3) := Equiv.swap 1 i
  have he1 : e 1 = i := Equiv.swap_apply_left _ _
  have hr := transverse_reindex e hE
  have hc := card_decomposition (reindex e E)
  have h0 := (hr 0).card_pos
  have h2 := (hr 2).card_pos
  have hsize' : (reindex e E).card ≤ 5 := by rwa [reindex_card]
  have h1 : (offsets (reindex e E) 1).card = 1 := by rw [offsets_reindex, he1, hi]
  have ha : (offsets (reindex e E) 0).card < 4 := by omega
  exact ⟨(e, ⟨_, ha⟩), h0, rfl, h1⟩

theorem type_card : Fintype.card TypeChoice = 24 := by
  simp only [TypeChoice, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  norm_num

theorem select {L : ℕ} (G : Finset (Finset (Vertex L)))
    (hG : ∀ E ∈ G, Transverse E ∧ E.card ≤ 5) (k : ℕ) (hk : 0 < k)
    (hpop : 24 * k ≤ G.card) :
    ∃ t : TypeChoice, ∃ F : Finset (Finset (Vertex L)), F ⊆ G ∧ F.card = k ∧ ∀ E ∈ F, Fits t E := by
  classical
  let U := fun t : TypeChoice ↦ G.filter (Fits t)
  have hcover : G ⊆ (univ : Finset TypeChoice).biUnion U := by
    intro E hE
    obtain ⟨t, ht⟩ := exists_type E (hG E hE).1 (hG E hE).2
    exact mem_biUnion.mpr ⟨t, mem_univ _, mem_filter.mpr ⟨hE, ht⟩⟩
  have hcard : G.card ≤ ∑ t : TypeChoice, (U t).card := (card_le_card hcover).trans card_biUnion_le
  have hlarge : ∃ t : TypeChoice, k ≤ (U t).card := by
    by_contra h
    have hu : ∀ t : TypeChoice, (U t).card ≤ k - 1 := by
      intro t
      have hh : ¬ k ≤ (U t).card := fun ht ↦ h ⟨t, ht⟩
      omega
    have hs := sum_le_sum (s := (univ : Finset TypeChoice)) (fun t _ ↦ hu t)
    have he : (∑ _t : TypeChoice, (k - 1)) = 24 * (k - 1) := by
      rw [sum_const, card_univ, type_card, nsmul_eq_mul]
      norm_num
    rw [he] at hs
    have hm : 24 * (k - 1) < 24 * k := Nat.mul_lt_mul_of_pos_left (by omega) (by decide)
    omega
  obtain ⟨t, ht⟩ := hlarge
  obtain ⟨F, hF, hFk⟩ := exists_subset_card_eq ht
  exact ⟨t, F, fun E hE ↦ (mem_filter.mp (hF hE)).1, hFk,
    fun E hE ↦ (mem_filter.mp (hF hE)).2⟩

end PaperP1.SmallTransverseSelection
