module

public import PaperP1.Model.SharedPrincipalTriples
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The actual ordered overlapping-edge contribution is bounded by nine times its triple mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPrincipalEdgePairs

open Finset PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (N H L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((PrincipalChannelEdges.edges N H L) ×ˢ (PrincipalChannelEdges.edges N H L)).filter
    fun p ↦ p.1 ≠ p.2 ∧ ¬Disjoint p.1 p.2

def contribution (N H L : ℕ) : ℝ := ∑ p ∈ pairs N H L, infiniteJointMoment L (p.1 ∪ p.2)

theorem union_mem_families {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N)
    {p : Finset ℕ × Finset ℕ} (hp : p ∈ pairs N H L) :
    p.1 ∪ p.2 ∈ SharedPrincipalTriples.families N H L := by
  obtain ⟨hbox, hne, hnd⟩ := mem_filter.mp hp
  obtain ⟨he, hf⟩ := mem_product.mp hbox
  have hsub := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (hsub he)
  obtain ⟨hfG, hfcard⟩ := mem_powersetCard.mp (hsub hf)
  have hTcard := TwoEdgeTripleCover.union_card_three hecard hfcard hne hnd
  have htwo : ({p.1, p.2} : Finset (Finset ℕ)) ⊆
      (PrincipalChannelEdges.edges N H L).filter fun e ↦ e ⊆ p.1 ∪ p.2 := by
    intro e he'
    rcases mem_insert.mp he' with rfl | he'
    · exact mem_filter.mpr ⟨he, subset_union_left⟩
    · rw [mem_singleton.mp he']
      exact mem_filter.mpr ⟨hf, subset_union_right⟩
  have hcount : 2 ≤ ((PrincipalChannelEdges.edges N H L).filter fun e ↦ e ⊆ p.1 ∪ p.2).card := by
    have hh := card_le_card htwo
    simpa only [card_pair hne] using hh
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨union_subset heG hfG, hTcard⟩, hcount⟩

theorem fibre_card {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N)
    {T : Finset ℕ} (hT : T.card = 3) :
    ((pairs N H L).filter fun p ↦ p.1 ∪ p.2 = T).card ≤ 9 := by
  have hsub : ((pairs N H L).filter fun p ↦ p.1 ∪ p.2 = T) ⊆ T.powersetCard 2 ×ˢ T.powersetCard 2 := by
    intro p hp
    obtain ⟨hpp, hunion⟩ := mem_filter.mp hp
    obtain ⟨hbox, _hne, _hnd⟩ := mem_filter.mp hpp
    obtain ⟨he, hf⟩ := mem_product.mp hbox
    have hall := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
    have heT : p.1 ⊆ T := by rw [← hunion]; exact subset_union_left
    have hfT : p.2 ⊆ T := by rw [← hunion]; exact subset_union_right
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨heT, (mem_powersetCard.mp (hall he)).2⟩,
      mem_powersetCard.mpr ⟨hfT, (mem_powersetCard.mp (hall hf)).2⟩⟩
  have hcard : (T.powersetCard 2).card = 3 := by rw [card_powersetCard, hT]; norm_num
  simpa only [card_product, hcard] using card_le_card hsub

theorem contribution_le_mass {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    contribution N H L ≤ 9 * SharedPrincipalTriples.mass N H L := by
  have hmap : (pairs N H L : Set (Finset ℕ × Finset ℕ)).MapsTo
      (fun p ↦ p.1 ∪ p.2) (SharedPrincipalTriples.families N H L) :=
    fun _ hp ↦ union_mem_families hN hlarge hp
  calc
    _ = ∑ T ∈ SharedPrincipalTriples.families N H L,
        ∑ p ∈ (pairs N H L).filter (fun p ↦ p.1 ∪ p.2 = T), infiniteJointMoment L (p.1 ∪ p.2) :=
      (sum_fiberwise_of_maps_to hmap (fun p ↦ infiniteJointMoment L (p.1 ∪ p.2))).symm
    _ = ∑ T ∈ SharedPrincipalTriples.families N H L,
        (((pairs N H L).filter fun p ↦ p.1 ∪ p.2 = T).card : ℝ) * infiniteJointMoment L T := by
      apply sum_congr rfl
      intro T _
      calc
        _ = ∑ _p ∈ (pairs N H L).filter (fun p ↦ p.1 ∪ p.2 = T), infiniteJointMoment L T :=
          sum_congr rfl (fun p hp ↦ congrArg (infiniteJointMoment L) (mem_filter.mp hp).2)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ T ∈ SharedPrincipalTriples.families N H L, 9 * infiniteJointMoment L T := by
      apply sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast fibre_card hN hlarge (SharedPrincipalTriples.family_data hT).2.1)
        (infiniteJointMoment_nonneg L T)
    _ = _ := by rw [SharedPrincipalTriples.mass, mul_sum]

theorem contribution_nonneg (N H L : ℕ) : 0 ≤ contribution N H L :=
  sum_nonneg (fun p _ ↦ infiniteJointMoment_nonneg L (p.1 ∪ p.2))

end PaperP1.SharedPrincipalEdgePairs
