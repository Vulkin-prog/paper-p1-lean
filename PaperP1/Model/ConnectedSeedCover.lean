module

public import PaperP1.Model.CrossingPairTriple
public import PaperP1.Model.ConnectedSpanCrossing
public import PaperP1.Model.LowTwoPairSeeds
public import PaperP1.Model.DensePairCrossingSeeds
public import PaperP1.Model.DirectCrossingSeedFamilies

/-! # An exhaustive actual seed cover of every nontrivial connected original-window family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedSeedCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

theorem cover (G : Finset ℕ) (L : ℕ) (a : ℝ) (ha : 0 ≤ a) (I : Finset ℕ)
    (hIG : I ⊆ G) (hsize : 3 ≤ I.card) (hconn : Connected L I) :
    (∃ D ⊆ I, Primitive L D ∧ 3 ≤ D.card) ∨
    (∃ T ⊆ I, T.card = 3 ∧ Connected L T) ∨
    (∃ T ∈ LowTwoPairSeeds.families G L a, T ⊆ I) ∨
    (∃ T ∈ DensePairCrossingSeeds.families G L a, T ⊆ I) ∨
    (∃ h : ℕ, 2 ≤ h ∧ h ≤ I.card - 2 ∧
      ∃ T ∈ DirectCrossingSeedFamilies.families G L h, T ⊆ I) := by
  classical
  obtain ⟨e, heI, hePrim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L I
    (CrossingPairTriple.connected_positive L I (by omega) hconn)
  by_cases heLarge : 3 ≤ e.card
  · exact Or.inl ⟨e, heI, hePrim, heLarge⟩
  have heTwo : e.card = 2 := by have h := PrimitiveActiveSeeds.primitive_card_ge_two L e hePrim; omega
  have heDep : 0 < runRelativeNullity L e := hePrim.1
  have heG : e ⊆ G := heI.trans hIG
  have heMem : e ∈ DependentFamilySeeds.dependentFamilies G L 2 :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨heG, heTwo⟩, heDep⟩
  have heProper : e ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨heI, fun h ↦ by rw [h] at heTwo; omega⟩
  obtain ⟨A, hAI, hANe, hcross, hproper⟩ := ConnectedSpanCrossing.exists_minimal L I e heProper
    (card_pos.mp (by omega : 0 < e.card)) hconn
  have hAG : A ⊆ G \ e := fun x hx ↦ mem_sdiff.mpr
    ⟨hIG (mem_sdiff.mp (hAI hx)).1, (mem_sdiff.mp (hAI hx)).2⟩
  have hAU : e ∪ A ⊆ I := union_subset heI (hAI.trans sdiff_subset)
  have hdis : Disjoint e A := disjoint_left.mpr fun x hxe hxA ↦ (mem_sdiff.mp (hAI hxA)).2 hxe
  have hACap : A.card ≤ I.card - 2 := by
    have h := card_le_card hAU
    rw [card_union_of_disjoint hdis, heTwo] at h
    omega
  have hlow_of (f : Finset ℕ) (hfA : f ⊆ A) (hfTwo : f.card = 2)
      (hfDep : 0 < runRelativeNullity L f)
      (hlow : (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) e ⊓
        span (fun x ↦ squareClassSpace x L) f) : ℝ) ≤ a * L) :
      ∃ T ∈ LowTwoPairSeeds.families G L a, T ⊆ I := by
    have hfG : f ⊆ G := hfA.trans (hAG.trans sdiff_subset)
    have hfMem : f ∈ DependentFamilySeeds.dependentFamilies G L 2 :=
      mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hfG, hfTwo⟩, hfDep⟩
    have hef : Disjoint e f := hdis.mono_right hfA
    refine ⟨e ∪ f, mem_image.mpr ⟨(e, f), ?_, rfl⟩, union_subset heI (hfA.trans (hAI.trans sdiff_subset))⟩
    exact (LowTwoPairSeeds.mem_sourcePairs G L a (e, f)).mpr ⟨heMem, hfMem, hef, hlow⟩
  by_cases hAOne : A.card = 1
  · obtain ⟨z, hAz⟩ := card_eq_one.mp hAOne
    have hzA : z ∈ A := by rw [hAz]; simp
    have hz : z ∉ e := (mem_sdiff.mp (hAI hzA)).2
    have hcrossZ : span (fun x ↦ squareClassSpace x L) e ⊓ squareClassSpace z L ≠ ⊥ := by
      have hs : span (fun x ↦ squareClassSpace x L) {z} = squareClassSpace z L := by simp [span]
      rw [hAz, hs] at hcross
      exact hcross
    right; left
    refine ⟨e ∪ {z}, by simpa only [hAz] using hAU, ?_, CrossingPairTriple.pair_extension L e heTwo heDep z hz hcrossZ⟩
    rw [card_union_of_disjoint (disjoint_singleton_right.mpr hz), heTwo, card_singleton]
  have hATwo : 2 ≤ A.card := by have h := card_pos.mpr hANe; omega
  by_cases hADirect : runRelativeNullity L A = 0
  · right; right; right; right
    refine ⟨A.card, hATwo, hACap, e ∪ A, mem_biUnion.mpr ⟨e, heMem, mem_image.mpr ⟨A, ?_, rfl⟩⟩, hAU⟩
    exact (DirectCrossingSeedFamilies.mem_targets G L A.card e A).mpr ⟨hAG, rfl, hADirect, hcross, hproper⟩
  obtain ⟨P, hPA, hPPrim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L A (Nat.pos_of_ne_zero hADirect)
  by_cases hPLarge : 3 ≤ P.card
  · exact Or.inl ⟨P, hPA.trans (hAI.trans sdiff_subset), hPPrim, hPLarge⟩
  have hPTwo : P.card = 2 := by have h := PrimitiveActiveSeeds.primitive_card_ge_two L P hPPrim; omega
  by_cases hPAEq : P = A
  · have hATwoEq : A.card = 2 := by rw [← hPAEq]; exact hPTwo
    have hADep : 0 < runRelativeNullity L A := Nat.pos_of_ne_zero hADirect
    by_cases hlow : (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) e ⊓
        span (fun x ↦ squareClassSpace x L) A) : ℝ) ≤ a * L
    · exact Or.inr (Or.inr (Or.inl (hlow_of A Subset.rfl hATwoEq hADep hlow)))
    · right; right; right; left
      obtain ⟨y, z, hyz, hAz⟩ := card_eq_two.mp hATwoEq
      have hyA : y ∈ A := by rw [hAz]; simp
      have hzA : z ∈ A := by rw [hAz]; simp
      have heq : TwoTargetFamilyCover.family e (y, z) = e ∪ A := by
        rw [hAz]
        simp only [TwoTargetFamilyCover.family, union_insert, union_singleton]
      refine ⟨e ∪ A, mem_biUnion.mpr ⟨e, heMem, mem_image.mpr ⟨(y, z), ?_, heq⟩⟩, hAU⟩
      apply (DensePairCrossingSeeds.mem_targets G L a e (y, z)).mpr
      refine ⟨(mem_sdiff.mp (hAG hyA)).1, (mem_sdiff.mp (hAG hzA)).1, hyz,
        (mem_sdiff.mp (hAG hyA)).2, (mem_sdiff.mp (hAG hzA)).2, ?_, ?_⟩
      · intro B hB
        exact hproper B (by simpa only [hAz] using hB)
      · change a * L ≤ (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) e ⊓
          span (fun x ↦ squareClassSpace x L) {y, z}) : ℝ)
        rw [← hAz]
        exact (lt_of_not_ge hlow).le
  · have hPProper : P ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hPA, hPAEq⟩
    have hzero := (hproper P hPProper).eq_bot
    have hlow : (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) e ⊓
        span (fun x ↦ squareClassSpace x L) P) : ℝ) ≤ a * L := by
      rw [hzero, finrank_bot, Nat.cast_zero]
      exact mul_nonneg ha (Nat.cast_nonneg _)
    exact Or.inr (Or.inr (Or.inl (hlow_of P hPA hPTwo hPPrim.1 hlow)))

end PaperP1.ConnectedSeedCover
