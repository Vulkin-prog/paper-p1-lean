module

public import PaperP1.Combinatorics.RetainedFamilyEnumeration
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Exact counts of direct and single-pair-compressed subfamilies of a retained configuration -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedSubsetCounts

open Finset PaperP1.Affine PaperP1.Algebra PaperP1.RetainedDependence PaperP1.RetainedFamilyEnumeration

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def directCount (A : Finset ι) (r : ℕ) : ℕ :=
  ((A.powersetCard r).filter fun I ↦ relativeNullityOn S I = 0).card

def compressedCount (A e : Finset ι) (r : ℕ) : ℕ :=
  ((A.powersetCard r).filter (Compressed S e)).card

def pairCount (E : Finset (Finset ι)) (A : Finset ι) (r : ℕ) : ℕ :=
  ∑ e ∈ E, compressedCount S A e r

omit [DecidableEq ι] in
theorem cardinality_filter (A : Finset ι) (P : Finset ι → Prop) (r : ℕ) :
    (A.powerset.filter P).filter (fun I ↦ I.card = r) = (A.powersetCard r).filter P := by
  ext I
  simp only [mem_filter, mem_powerset, mem_powersetCard]
  tauto

theorem choose_decomposition (E : Finset (Finset ι))
    (hcard : ∀ e ∈ E, e.card = 2) (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e)
    (A : Finset ι) (hA : Retained S E A) (r : ℕ) :
    A.card.choose r = directCount S A r + pairCount S E A r := by
  have hsets : retainedSets A (Retained S E) = A.powerset := by
    ext I
    simp only [retainedSets, mem_filter]
    exact ⟨And.left, fun h ↦ ⟨h, hereditary S E hcard (mem_powerset.mp h) hA⟩⟩
  have hsum : (∑ I ∈ retainedSets A (Retained S E), if I.card = r then (1 : ℕ) else 0) =
      (∑ I ∈ directFamilies S A, if I.card = r then 1 else 0) +
      ∑ e ∈ E, ∑ I ∈ compressedFamilies S A e, if I.card = r then 1 else 0 := by
    rw [retained_split S A E, sum_union (direct_disjoint_compressed S A E hpos),
      sum_biUnion (compressed_pairwise_disjoint S A E hcard hpos)]
  have htotal : (∑ I ∈ retainedSets A (Retained S E), if I.card = r then (1 : ℕ) else 0) = A.card.choose r := by
    rw [hsets, sum_boole, Nat.cast_id, ← card_powersetCard r A]
    congr 1
    ext I
    simp only [mem_filter, mem_powerset, mem_powersetCard]
  have hdirect : (∑ I ∈ directFamilies S A, if I.card = r then (1 : ℕ) else 0) = directCount S A r := by
    rw [sum_boole, Nat.cast_id]
    unfold directCount
    congr 1
    ext I
    simp only [directFamilies, mem_filter, mem_powerset, mem_powersetCard]
    tauto
  have hcompressed (e : Finset ι) : (∑ I ∈ compressedFamilies S A e, if I.card = r then (1 : ℕ) else 0) = compressedCount S A e r := by
    rw [sum_boole, Nat.cast_id]
    unfold compressedCount
    congr 1
    ext I
    simp only [compressedFamilies, mem_filter, mem_powerset, mem_powersetCard]
    tauto
  rw [htotal, hdirect] at hsum
  simp_rw [hcompressed] at hsum
  exact hsum

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem directCount_le_choose (A : Finset ι) (r : ℕ) : directCount S A r ≤ A.card.choose r :=
  (card_le_card (filter_subset _ _)).trans_eq (card_powersetCard r A)

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem compressedCount_le_choose (A e : Finset ι) (r : ℕ) : compressedCount S A e r ≤ A.card.choose r :=
  (card_le_card (filter_subset _ _)).trans_eq (card_powersetCard r A)

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem compressedCount_zero_of_not_subset (A e : Finset ι) (r : ℕ) (he : ¬e ⊆ A) :
    compressedCount S A e r = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro I hI
  obtain ⟨hIA, hcomp⟩ := mem_filter.mp hI
  exact he (hcomp.1.trans (mem_powersetCard.mp hIA).1)

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem pairCount_zero_small (E : Finset (Finset ι)) (hcard : ∀ e ∈ E, e.card = 2)
    (A : Finset ι) (r : ℕ) (hr : r < 2) : pairCount S E A r = 0 := by
  apply sum_eq_zero
  intro e he
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro I hI
  obtain ⟨hIA, hcomp⟩ := mem_filter.mp hI
  have hle := card_le_card hcomp.1
  rw [hcard e he, (mem_powersetCard.mp hIA).2] at hle
  omega

omit [∀ i, Fintype (S i)] in
theorem pairCount_le_power (E : Finset (Finset ι)) (hcard : ∀ e ∈ E, e.card = 2)
    (A : Finset ι) (r : ℕ) : pairCount S E A r ≤ A.card ^ (r + 2) := by
  let EA := E.filter fun e ↦ e ⊆ A
  have heq : pairCount S E A r = ∑ e ∈ EA, compressedCount S A e r := by
    symm
    apply sum_subset (filter_subset _ _)
    intro e _he hnot
    apply compressedCount_zero_of_not_subset S A e r
    intro hsub
    exact hnot (mem_filter.mpr ⟨_he, hsub⟩)
  have hsub : EA ⊆ A.powersetCard 2 := fun e he ↦ mem_powersetCard.mpr
    ⟨(mem_filter.mp he).2, hcard e (mem_filter.mp he).1⟩
  have hc : EA.card ≤ A.card ^ 2 :=
    ((card_le_card hsub).trans_eq (card_powersetCard 2 A)).trans (Nat.choose_le_pow A.card 2)
  calc
    _ = ∑ e ∈ EA, compressedCount S A e r := heq
    _ ≤ ∑ _e ∈ EA, A.card ^ r := sum_le_sum fun e _ ↦
      (compressedCount_le_choose S A e r).trans (Nat.choose_le_pow A.card r)
    _ = EA.card * A.card ^ r := by simp only [sum_const, smul_eq_mul]
    _ ≤ A.card ^ 2 * A.card ^ r := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add]; congr 1; omega

omit [∀ i, Fintype (S i)] in
theorem compressed_layer_reindex {R : Type*} [AddCommMonoid R] (G e : Finset ι)
    (heG : e ⊆ G) (he : e.card = 2) (r : ℕ) (hr : 2 ≤ r) (f : Finset ι → R) :
    (∑ I ∈ (G.powersetCard r).filter (Compressed S e), f I) =
      ∑ A ∈ ((G \ e).powersetCard (r - 2)).filter (fun A ↦ Compressed S e (e ∪ A)), f (e ∪ A) := by
  symm
  apply sum_bij (fun A _ ↦ e ∪ A)
  · intro A hA
    obtain ⟨hAG, hcomp⟩ := mem_filter.mp hA
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hAG
    have hdis := extension_disjoint G e A hsub
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨union_subset heG (hsub.trans sdiff_subset), ?_⟩, hcomp⟩
    rw [card_union_of_disjoint hdis, he, hcard]
    omega
  · intro A hA B hB heq
    have hAdis := extension_disjoint G e A (mem_powersetCard.mp (mem_filter.mp hA).1).1
    have hBdis := extension_disjoint G e B (mem_powersetCard.mp (mem_filter.mp hB).1).1
    have h := congrArg (fun I : Finset ι ↦ I \ e) heq
    simpa only [union_sdiff_cancel_left hAdis, union_sdiff_cancel_left hBdis] using h
  · intro I hI
    obtain ⟨hIG, hcomp⟩ := mem_filter.mp hI
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
    have heq := union_sdiff_of_subset hcomp.1
    refine ⟨I \ e, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset_sdiff_left e hsub, ?_⟩, ?_⟩, heq⟩
    · rw [card_sdiff_of_subset hcomp.1, hcard, he]
    · rw [heq]
      exact hcomp
  · intro A _hA
    rfl

end PaperP1.RetainedSubsetCounts
