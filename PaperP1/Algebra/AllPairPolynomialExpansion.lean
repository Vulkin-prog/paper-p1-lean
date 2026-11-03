module

public import PaperP1.Algebra.RetainedReferenceIdentity

/-! # Exact expansion of the heterogeneous independent reference plus every signed pair correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairPolynomialExpansion

open Finset PaperP1.RetainedReferenceIdentity

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

theorem complement_generator (G D : Finset ι) (hDG : D ⊆ G) (w : ι → R) :
    (∑ I ∈ G.powerset.filter (fun I ↦ D ⊆ I), ∏ x ∈ I \ D, w x) = ∏ x ∈ G \ D, (1 + w x) := by
  classical
  rw [prod_one_add]
  symm
  apply sum_bij (fun A _ ↦ D ∪ A)
  · intro A hA
    have hAG := mem_powerset.mp hA
    exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset hDG (hAG.trans sdiff_subset)), subset_union_left⟩
  · intro A hA B hB heq
    have hAdis : Disjoint D A := disjoint_left.mpr
      (fun x hxD hxA ↦ (mem_sdiff.mp (mem_powerset.mp hA hxA)).2 hxD)
    have hBdis : Disjoint D B := disjoint_left.mpr
      (fun x hxD hxB ↦ (mem_sdiff.mp (mem_powerset.mp hB hxB)).2 hxD)
    have h := congrArg (fun I : Finset ι ↦ I \ D) heq
    simpa only [union_sdiff_cancel_left hAdis, union_sdiff_cancel_left hBdis] using h
  · intro I hI
    obtain ⟨hIG, hDI⟩ := mem_filter.mp hI
    exact ⟨I \ D, mem_powerset.mpr (sdiff_subset_sdiff_left D (mem_powerset.mp hIG)), union_sdiff_of_subset hDI⟩
  · intro A hA
    have hAdis : Disjoint D A := disjoint_left.mpr
      (fun x hxD hxA ↦ (mem_sdiff.mp (mem_powerset.mp hA hxA)).2 hxD)
    rw [union_sdiff_cancel_left hAdis]

theorem source_expansion (G e : Finset ι) (heG : e ⊆ G) (he : e.card = 2) (p : ι → R) (c t : R) :
    c * t ^ 2 * (∏ x ∈ G \ e, (1 + p x * t)) =
      ∑ I ∈ G.powerset, if e ⊆ I then (c * ∏ x ∈ I \ e, p x) * t ^ I.card else 0 := by
  classical
  rw [← complement_generator G e heG (fun x ↦ p x * t), mul_sum, sum_filter]
  apply sum_congr rfl
  intro I _hI
  by_cases heI : e ⊆ I
  · rw [ite_eq_left heI, ite_eq_left heI, prod_mul_distrib, prod_const]
    have hcard : I.card = 2 + (I \ e).card := by have h := card_sdiff_add_card_eq_card heI; omega
    rw [hcard, pow_add]
    ring
  · rw [ite_eq_right heI, ite_eq_right heI]

theorem all_pair_expansion (G : Finset ι) (p : ι → R) (c : Finset ι → R) (t : R) :
    (∏ x ∈ G, (1 + p x * t)) +
        (∑ e ∈ G.powersetCard 2, c e * t ^ 2 * ∏ x ∈ G \ e, (1 + p x * t)) =
      ∑ I ∈ G.powerset, ((∏ x ∈ I, p x) + ∑ e ∈ I.powersetCard 2, c e * ∏ x ∈ I \ e, p x) * t ^ I.card := by
  classical
  have hind : (∏ x ∈ G, (1 + p x * t)) = ∑ I ∈ G.powerset, (∏ x ∈ I, p x) * t ^ I.card := by
    rw [prod_one_add]
    apply sum_congr rfl
    intro I _hI
    rw [prod_mul_distrib, prod_const]
  rw [hind]
  have hsource : (∑ e ∈ G.powersetCard 2, c e * t ^ 2 * ∏ x ∈ G \ e, (1 + p x * t)) =
      ∑ e ∈ G.powersetCard 2, ∑ I ∈ G.powerset,
        if e ⊆ I then (c e * ∏ x ∈ I \ e, p x) * t ^ I.card else 0 := by
    apply sum_congr rfl
    intro e he
    exact source_expansion G e (mem_powersetCard.mp he).1 (mem_powersetCard.mp he).2 p (c e) t
  rw [hsource, sum_comm, ← sum_add_distrib]
  apply sum_congr rfl
  intro I hI
  have hfilter : (G.powersetCard 2).filter (fun e ↦ e ⊆ I) = I.powersetCard 2 := by
    ext e
    simp only [mem_filter, mem_powersetCard]
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.trans (mem_powerset.mp hI), h.2⟩, h.1⟩⟩
  rw [add_mul, sum_mul, ← hfilter, sum_filter]

end PaperP1.AllPairPolynomialExpansion
