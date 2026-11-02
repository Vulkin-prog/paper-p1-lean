module

public import PaperP1.Affine.CompressedRelationSupport

/-! # Exact, disjoint enumeration of direct families and one compressed pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedFamilyEnumeration

open Finset PaperP1.Affine PaperP1.RetainedDependence PaperP1.Algebra

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def directFamilies (G : Finset κ) : Finset (Finset κ) := by
  classical
  exact G.powerset.filter (fun I ↦ relativeNullityOn S I = 0)

def compressedFamilies (G e : Finset κ) : Finset (Finset κ) := by
  classical
  exact G.powerset.filter (Compressed S e)

def extensions (G e : Finset κ) : Finset (Finset κ) := by
  classical
  exact (G \ e).powerset.filter (fun A ↦ Compressed S e (e ∪ A))

omit [∀ i, Fintype (S i)] in
theorem retained_split (G : Finset κ) (E : Finset (Finset κ)) :
    retainedSets G (Retained S E) = directFamilies S G ∪ E.biUnion (compressedFamilies S G) := by
  classical
  ext I
  simp only [retainedSets, directFamilies, compressedFamilies, mem_filter, mem_powerset,
    mem_union, mem_biUnion, Retained]
  constructor
  · rintro ⟨hIG, hzero | ⟨e, he, hcomp⟩⟩
    · exact Or.inl ⟨hIG, hzero⟩
    · exact Or.inr ⟨e, he, hIG, hcomp⟩
  · rintro (⟨hIG, hzero⟩ | ⟨e, he, hIG, hcomp⟩)
    · exact ⟨hIG, Or.inl hzero⟩
    · exact ⟨hIG, Or.inr ⟨e, he, hcomp⟩⟩

omit [∀ i, Fintype (S i)] in
theorem direct_disjoint_compressed (G : Finset κ) (E : Finset (Finset κ))
    (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e) :
    Disjoint (directFamilies S G) (E.biUnion (compressedFamilies S G)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro I hdir hcompressed
  have hzero := (mem_filter.mp hdir).2
  obtain ⟨e, he, hI⟩ := mem_biUnion.mp hcompressed
  have hcomp := (mem_filter.mp hI).2
  have hp := hpos e he
  have heq := hcomp.2
  omega

theorem compressed_pair_unique (E : Finset (Finset κ)) (hcard : ∀ e ∈ E, e.card = 2)
    (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e) (I e f : Finset κ)
    (he : e ∈ E) (hf : f ∈ E) (heI : Compressed S e I) (hfI : Compressed S f I) : e = f := by
  have hret : Retained S E I := Or.inr ⟨e, he, heI⟩
  have hnonzero : relativeNullityOn S I ≠ 0 := by have hp := hpos e he; have h := heI.2; omega
  obtain ⟨g, _hg, _hcomp, _hgpos, huniq⟩ := dependent_pair_unique S E hcard I hret hnonzero
  exact (huniq e heI.1 (hcard e he) (hpos e he)).trans
    (huniq f hfI.1 (hcard f hf) (hpos f hf)).symm

theorem compressed_pairwise_disjoint (G : Finset κ) (E : Finset (Finset κ))
    (hcard : ∀ e ∈ E, e.card = 2) (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e) :
    Set.PairwiseDisjoint (E : Set (Finset κ)) (compressedFamilies S G) := by
  classical
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro I heI hfI
  exact hne (compressed_pair_unique S E hcard hpos I e f he hf
    (mem_filter.mp heI).2 (mem_filter.mp hfI).2)

theorem extension_disjoint (G e A : Finset κ) (hA : A ⊆ G \ e) : Disjoint e A := by
  apply Finset.disjoint_left.mpr
  intro x hxe hxA
  exact (mem_sdiff.mp (hA hxA)).2 hxe

omit [∀ i, Fintype (S i)] in
theorem compressed_sum_reindex {R : Type*} [AddCommMonoid R] (G e : Finset κ)
    (heG : e ⊆ G) (f : Finset κ → R) :
    (∑ I ∈ compressedFamilies S G e, f I) = ∑ A ∈ extensions S G e, f (e ∪ A) := by
  classical
  symm
  apply sum_bij (fun A _hA ↦ e ∪ A)
  · intro A hA
    obtain ⟨hA, hcomp⟩ := mem_filter.mp hA
    have hsub := mem_powerset.mp hA
    exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset heG (hsub.trans sdiff_subset)), hcomp⟩
  · intro A hA B hB heq
    have hAdis := extension_disjoint G e A (mem_powerset.mp (mem_filter.mp hA).1)
    have hBdis := extension_disjoint G e B (mem_powerset.mp (mem_filter.mp hB).1)
    have h := congrArg (fun I : Finset κ ↦ I \ e) heq
    simpa only [union_sdiff_cancel_left hAdis, union_sdiff_cancel_left hBdis] using h
  · intro I hI
    obtain ⟨hIG, hcomp⟩ := mem_filter.mp hI
    have hsub := mem_powerset.mp hIG
    have heq : e ∪ I \ e = I := union_sdiff_of_subset hcomp.1
    refine ⟨I \ e, mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset_sdiff_left e hsub), ?_⟩, heq⟩
    rw [heq]
    exact hcomp
  · intro A _hA
    rfl

theorem retained_sum_decomposition {R : Type*} [AddCommMonoid R]
    (G : Finset κ) (E : Finset (Finset κ)) (hcard : ∀ e ∈ E, e.card = 2)
    (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e) (hground : ∀ e ∈ E, e ⊆ G)
    (f : Finset κ → R) :
    (∑ I ∈ retainedSets G (Retained S E), f I) = (∑ I ∈ directFamilies S G, f I) +
      ∑ e ∈ E, ∑ A ∈ extensions S G e, f (e ∪ A) := by
  classical
  rw [retained_split, sum_union (direct_disjoint_compressed S G E hpos),
    sum_biUnion (compressed_pairwise_disjoint S G E hcard hpos)]
  congr 1
  apply sum_congr rfl
  intro e he
  exact compressed_sum_reindex S G e (hground e he) f

end PaperP1.RetainedFamilyEnumeration
