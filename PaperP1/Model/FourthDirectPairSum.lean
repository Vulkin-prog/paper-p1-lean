module

public import PaperP1.Model.CanonicalPairImages
public import PaperP1.Model.DirectPairProductComparison

/-! # Exact identification of the disconnected quartic sum with unordered direct pair products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthDirectPairSum

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.DirectPairProductComparison

def disconnectedFamilies (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard 4).filter (fun I ↦ ¬ConnectedWindowFamilies.Connected L I)

def canonicalParts (L : ℕ) (I : Finset ℕ) : Finset (Finset ℕ) :=
  (canonicalRelationPartition (fun i : I ↦ squareClassSpace i.val L)).parts.image
    (fun C : Finset I ↦ FinitePartImage.image C)

theorem pair_mem_direct_iff (G : Finset ℕ) (L : ℕ) (e f : Finset ℕ)
    (he : e ∈ G.powersetCard 2) (hf : f ∈ G.powersetCard 2) (hef : e ≠ f) :
    {e, f} ∈ directPairs G L ↔ Disjoint e f ∧
      runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f := by
  classical
  have hbase : {e, f} ∈ (G.powersetCard 2).powersetCard 2 := mem_powersetCard.mpr
    ⟨by intro d hd; simp only [mem_insert, mem_singleton] at hd
        rcases hd with rfl | rfl <;> assumption,
      by simp [hef]⟩
  simp only [directPairs, mem_filter, hbase, true_and,
    SharedPairProducts.pair_mem_overlapping G e f he hf hef,
    not_not, direct_pair_iff L e f hef]

theorem direct_pair_data (G : Finset ℕ) (L : ℕ) (S : Finset (Finset ℕ))
    (hS : S ∈ directPairs G L) :
    ∃ e f : Finset ℕ, e ≠ f ∧ S = {e, f} ∧ e ∈ G.powersetCard 2 ∧ f ∈ G.powersetCard 2 ∧
      Disjoint e f ∧ runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f := by
  classical
  have hbase := (mem_filter.mp hS).1
  obtain ⟨hSE, hcard⟩ := mem_powersetCard.mp hbase
  obtain ⟨e, f, hef, hpair⟩ := card_eq_two.mp hcard
  have he : e ∈ G.powersetCard 2 := hSE (by rw [hpair]; simp)
  have hf : f ∈ G.powersetCard 2 := hSE (by rw [hpair]; simp)
  have hdata := (pair_mem_direct_iff G L e f he hf hef).mp (hpair ▸ hS)
  exact ⟨e, f, hef, hpair, he, hf, hdata⟩

theorem union_mem_disconnected (G : Finset ℕ) (L : ℕ) (S : Finset (Finset ℕ))
    (hS : S ∈ directPairs G L) : S.biUnion id ∈ disconnectedFamilies G L := by
  classical
  obtain ⟨e, f, _hef, hpair, he, hf, hdis, hnull⟩ := direct_pair_data G L S hS
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp he
  obtain ⟨hfG, hfcard⟩ := mem_powersetCard.mp hf
  rw [hpair]
  simp only [biUnion_insert, singleton_biUnion, id_eq]
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨union_subset heG hfG, ?_⟩,
    DirectRunBlocks.not_connected L e f (card_pos.mp (by omega)) (card_pos.mp (by omega)) hdis hnull⟩
  rw [card_union_of_disjoint hdis, hecard, hfcard]

theorem product_eq_union (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (S : Finset (Finset ℕ))
    (hS : S ∈ directPairs G L) :
    (∏ e ∈ S, infiniteCenteredCoefficient L e) = infiniteCenteredCoefficient L (S.biUnion id) := by
  classical
  obtain ⟨e, f, hef, hpair, he, hf, hdis, hnull⟩ := direct_pair_data G L S hS
  rw [hpair, prod_pair hef, biUnion_insert, singleton_biUnion, id_eq]
  exact (DirectRunBlocks.centered_factor L hL e f
    (card_pos.mp (by rw [(mem_powersetCard.mp he).2]; norm_num))
    (card_pos.mp (by rw [(mem_powersetCard.mp hf).2]; norm_num)) hdis hnull).symm

set_option maxHeartbeats 1000000 in
theorem canonical_images_eq (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (S : Finset (Finset ℕ))
    (hS : S ∈ directPairs G L) (hc : infiniteCenteredCoefficient L (S.biUnion id) ≠ 0) :
    canonicalParts L (S.biUnion id) = S := by
  classical
  obtain ⟨e, f, _hef, hpair, he, hf, hdis, hnull⟩ := direct_pair_data G L S hS
  rw [hpair] at hc ⊢
  simp only [biUnion_insert, singleton_biUnion, id_eq] at hc ⊢
  exact CanonicalPairImages.canonical_images L hL e f
    (mem_powersetCard.mp he).2 (mem_powersetCard.mp hf).2 hdis hnull hc

theorem union_injective_nonzero (G : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (S T : Finset (Finset ℕ)) (hS : S ∈ directPairs G L) (hT : T ∈ directPairs G L)
    (hcS : (∏ e ∈ S, infiniteCenteredCoefficient L e) ≠ 0)
    (hcT : (∏ e ∈ T, infiniteCenteredCoefficient L e) ≠ 0)
    (hunion : S.biUnion id = T.biUnion id) : S = T := by
  have hS' : infiniteCenteredCoefficient L (S.biUnion id) ≠ 0 := by
    rwa [← product_eq_union G L hL S hS]
  have hT' : infiniteCenteredCoefficient L (T.biUnion id) ≠ 0 := by
    rwa [← product_eq_union G L hL T hT]
  have hcanon := congrArg (canonicalParts L) hunion
  rwa [canonical_images_eq G L hL S hS hS', canonical_images_eq G L hL T hT hT'] at hcanon

theorem disconnected_preimage (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hI : I ∈ disconnectedFamilies G L) (hc : infiniteCenteredCoefficient L I ≠ 0) :
    ∃ S ∈ directPairs G L, (∏ e ∈ S, infiniteCenteredCoefficient L e) ≠ 0 ∧ S.biUnion id = I := by
  classical
  obtain ⟨hI, hconn⟩ := mem_filter.mp hI
  obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp hI
  obtain ⟨e, f, hecard, hfcard, hdis, hcover, hnull, hfactor⟩ :=
    FourthRunComponents.disconnected_factorization L hL I hcard hc hconn
  have heG : e ⊆ G := (show e ⊆ I from hcover ▸ subset_union_left).trans hIG
  have hfG : f ⊆ G := (show f ⊆ I from hcover ▸ subset_union_right).trans hIG
  have hef : e ≠ f := by
    intro h
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < e.card by omega)
    exact disjoint_left.mp hdis hx (h ▸ hx)
  have hS : {e, f} ∈ directPairs G L := (pair_mem_direct_iff G L e f
    (mem_powersetCard.mpr ⟨heG, hecard⟩) (mem_powersetCard.mpr ⟨hfG, hfcard⟩) hef).mpr
      ⟨hdis, by rw [hcover]; exact hnull⟩
  refine ⟨{e, f}, hS, ?_, ?_⟩
  · rw [prod_pair hef, ← hfactor]
    exact hc
  · simpa only [biUnion_insert, singleton_biUnion, id_eq] using hcover

theorem signedDirect_eq_disconnected (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    signedDirect G L = CompatibleActivitySplit.signed L (disconnectedFamilies G L) := by
  classical
  apply sum_bij_ne_zero (fun S _ _ ↦ S.biUnion id)
  · intro S hS _
    exact union_mem_disconnected G L S hS
  · intro S hS hcS T hT hcT hST
    exact union_injective_nonzero G L hL S T hS hT hcS hcT hST
  · intro I hI hc
    obtain ⟨S, hS, hcS, hU⟩ := disconnected_preimage G L hL I hI hc
    exact ⟨S, hS, hcS, hU⟩
  · intro S hS _
    exact product_eq_union G L hL S hS

theorem quartic_split (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.signed L (G.powersetCard 4) =
      CompatibleActivitySplit.signed L (ConnectedWindowFamilies.connectedFamilies G L 4) + signedDirect G L := by
  classical
  rw [signedDirect_eq_disconnected G L hL]
  exact (sum_filter_add_sum_filter_not (G.powersetCard 4)
    (ConnectedWindowFamilies.Connected L) (infiniteCenteredCoefficient L)).symm

end PaperP1.FourthDirectPairSum
