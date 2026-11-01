module

public import PaperP1.Arithmetic.LocalRelationSets
public import PaperP1.Model.RegularStarts
public import Mathlib.Data.Finset.Max

/-! # The exact interval of starts containing a physical local square relation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRelationBlocks

open Finset PaperP1.LocalRelationSets PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.WindowRelationCode PaperP1.RegularStarts

def first (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.min' h else 0

def last (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.max' h else 0

def fullBlock (L : ℕ) (S : Finset ℕ) : Finset ℕ := Icc (last S - L + 1) (first S + 1)

def block (N L : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ S ⊆ window x L

def relations (N L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Ico (N - 1) (2 * N + L)).powerset.filter fun S ↦
    Relation S ∧ ∃ x ∈ dyadicBlock N, S ⊆ window x L

theorem first_mem {S : Finset ℕ} (hS : S.Nonempty) : first S ∈ S := by
  simpa only [first, dite_eq_left hS] using S.min'_mem hS

theorem last_mem {S : Finset ℕ} (hS : S.Nonempty) : last S ∈ S := by
  simpa only [last, dite_eq_left hS] using S.max'_mem hS

theorem first_le {S : Finset ℕ} (hS : S.Nonempty) {n : ℕ} (hn : n ∈ S) : first S ≤ n := by
  simpa only [first, dite_eq_left hS] using S.min'_le n hn

theorem le_last {S : Finset ℕ} (hS : S.Nonempty) {n : ℕ} (hn : n ∈ S) : n ≤ last S := by
  simpa only [last, dite_eq_left hS] using S.le_max' n hn

theorem first_le_last {S : Finset ℕ} (hS : S.Nonempty) : first S ≤ last S := first_le hS (last_mem hS)

theorem relation_card_ge_two {S : Finset ℕ} (hS : Relation S) : 2 ≤ S.card := by
  have hpos := card_pos.mpr hS.1
  obtain ⟨k, hk⟩ := hS.2.1
  omega

theorem relation_first_lt_last {S : Finset ℕ} (hS : Relation S) : first S < last S := by
  simpa only [first, last, dite_eq_left hS.1] using
    S.min'_lt_max'_of_card (by have h := relation_card_ge_two hS; omega)

theorem mem_block (N L : ℕ) (S : Finset ℕ) (x : ℕ) :
    x ∈ block N L S ↔ x ∈ dyadicBlock N ∧ S ⊆ window x L := mem_filter

theorem mem_relations (N L : ℕ) (S : Finset ℕ) :
    S ∈ relations N L ↔ Relation S ∧ ∃ x ∈ dyadicBlock N, S ⊆ window x L := by
  classical
  constructor
  · intro hS
    exact (mem_filter.mp hS).2
  · rintro ⟨hrel, x, hx, hS⟩
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_, hrel, x, hx, hS⟩
    intro n hn
    have hnwin := mem_Ico.mp (hS hn)
    have hxb := mem_Ico.mp hx
    exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem block_nonempty {N L : ℕ} {S : Finset ℕ} (hS : S ∈ relations N L) : (block N L S).Nonempty := by
  obtain ⟨_, x, hx, hwin⟩ := (mem_relations N L S).mp hS
  exact ⟨x, (mem_block N L S x).mpr ⟨hx, hwin⟩⟩

theorem mem_relations_iff_square_product {N L : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) :
    S ∈ relations N L ↔ S.Nonempty ∧ Even S.card ∧ (∃ r : ℕ, S.prod id = r ^ 2) ∧
      ∃ x ∈ dyadicBlock N, S ⊆ window x L := by
  constructor
  · intro hS
    obtain ⟨hrel, x, hx, hwin⟩ := (mem_relations N L S).mp hS
    have hpos (n : ℕ) (hn : n ∈ S) : 0 < n := by
      have h := (mem_Ico.mp (hwin hn)).1
      have hxN := (mem_Ico.mp hx).1
      omega
    obtain ⟨hne, heven, hsquare⟩ := (relation_iff_square_product S hpos).mp hrel
    exact ⟨hne, heven, hsquare, x, hx, hwin⟩
  · rintro ⟨hne, heven, hsquare, x, hx, hwin⟩
    have hpos (n : ℕ) (hn : n ∈ S) : 0 < n := by
      have h := (mem_Ico.mp (hwin hn)).1
      have hxN := (mem_Ico.mp hx).1
      omega
    exact (mem_relations N L S).mpr ⟨(relation_iff_square_product S hpos).mpr
      ⟨hne, heven, hsquare⟩, x, hx, hwin⟩

theorem subset_window_iff {x L : ℕ} (hx : 0 < x) (S : Finset ℕ) (hS : S.Nonempty) :
    S ⊆ window x L ↔ x ≤ first S + 1 ∧ last S < x + L := by
  constructor
  · intro h
    have hlo := (mem_Ico.mp (h (first_mem hS))).1
    have hhi := (mem_Ico.mp (h (last_mem hS))).2
    exact ⟨by omega, hhi⟩
  · rintro ⟨hlo, hhi⟩ n hn
    have hfirst := first_le hS hn
    have hlast := le_last hS hn
    exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem block_eq_interval {N L : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) (hS : S.Nonempty)
    (hL : L ≤ last S) : block N L S = fullBlock L S ∩ dyadicBlock N := by
  ext x
  constructor
  · intro hx
    obtain ⟨hbox, hwin⟩ := (mem_block N L S x).mp hx
    have hxpos : 0 < x := by have h := (mem_Ico.mp hbox).1; omega
    obtain ⟨hlo, hhi⟩ := (subset_window_iff hxpos S hS).mp hwin
    exact mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega, hlo⟩, hbox⟩
  · intro hx
    obtain ⟨hfull, hbox⟩ := mem_inter.mp hx
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hfull
    have hxpos : 0 < x := by have h := (mem_Ico.mp hbox).1; omega
    apply (mem_block N L S x).mpr
    exact ⟨hbox, (subset_window_iff hxpos S hS).mpr ⟨hhi, by omega⟩⟩

theorem last_ge_length {N L : ℕ} (hN : L + 1 ≤ N) {S : Finset ℕ} (hS : S ∈ relations N L) : L ≤ last S := by
  obtain ⟨hrel, x, hx, hwin⟩ := (mem_relations N L S).mp hS
  have hfirst := (mem_Ico.mp (hwin (last_mem hrel.1))).1
  have hxN := (mem_Ico.mp hx).1
  omega

theorem relation_iff_rank_defect {x L : ℕ} (hx : 0 < x) :
    Module.finrank F₂ (squareClassSpace x L) < L ↔ ∃ S : Finset ℕ, Relation S ∧ S ⊆ window x L := by
  have hrank := PaperP1.LocalRunRank.squareClass_rank_add_relation_rank (L := L) hx
  constructor
  · intro hdef
    have hpos : 0 < Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) := by omega
    obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨physicalSupport x L w.val, relation_support hx w hw, support_subset_window hx w.val⟩
  · rintro ⟨S, hrel, hwin⟩
    let w : windowRelationCode (x - 1) (L + 1) := ⟨word x L S, word_mem_code hx S hwin hrel⟩
    have hw : w ≠ 0 := fun h ↦ word_ne_zero hx S hwin hrel.1 (congrArg Subtype.val h)
    have hpos : 0 < Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w, hw⟩
    omega

theorem blocks_disjoint {N L : ℕ} (hN : 2 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S T : Finset ℕ} (hS : S ∈ relations N L) (hT : T ∈ relations N L) (hne : S ≠ T) :
    Disjoint (block N L S) (block N L T) := by
  apply disjoint_left.mpr
  intro x hxS hxT
  obtain ⟨hx, hwinS⟩ := (mem_block N L S x).mp hxS
  have hwinT := ((mem_block N L T x).mp hxT).2
  have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
  exact hne (unique_relation_in_window hxpos (hrank x hx) S T hwinS hwinT
    ((mem_relations N L S).mp hS).1 ((mem_relations N L T).mp hT).1)

theorem blocks_cover_irregular {N L : ℕ} (hN : 2 ≤ N) :
    (relations N L).biUnion (block N L) = irregularStarts N L := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hx
    obtain ⟨hx, hwin⟩ := (mem_block N L S x).mp hxS
    have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
    have hdef := (relation_iff_rank_defect hxpos).mpr ⟨S, ((mem_relations N L S).mp hS).1, hwin⟩
    exact mem_irregularStarts.mpr ⟨hx, hdef.ne⟩
  · intro hx
    obtain ⟨hx, hnot⟩ := mem_irregularStarts.mp hx
    have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
    have hdef : Module.finrank F₂ (squareClassSpace x L) < L :=
      lt_of_le_of_ne (PaperP1.LocalRunRank.squareClass_rank_le x L hxpos) hnot
    obtain ⟨S, hrel, hwin⟩ := (relation_iff_rank_defect hxpos).mp hdef
    exact mem_biUnion.mpr ⟨S, (mem_relations N L S).mpr ⟨hrel, x, hx, hwin⟩,
      (mem_block N L S x).mpr ⟨hx, hwin⟩⟩

end PaperP1.LocalRelationBlocks
