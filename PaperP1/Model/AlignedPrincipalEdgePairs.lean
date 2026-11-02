module

public import PaperP1.Asymptotics.AlignedTripleExtensions
public import PaperP1.Model.PrincipalEdgeSpaces
public import PaperP1.Model.PrincipalEdgeGeometry

/-! # The literal four-vertex principal-edge sector containing an aligned triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedPrincipalEdgePairs

open Finset PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def HasSeed (N L J : ℕ) (I : Finset ℕ) : Prop :=
  ∃ T ∈ AlignedTripleExtensions.seeds PrincipalEdgeGeometry.channels (fun _ ↦ J) N L, T ⊆ I

def pairs (N H L J : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (PrincipalEdgeSpaces.factorialPairs N H L).filter fun p ↦ Disjoint p.1 p.2 ∧ HasSeed N L J (p.1 ∪ p.2)

def contribution (N H L J : ℕ) : ℝ :=
  ∑ p ∈ pairs N H L J, infiniteJointMoment L (p.1 ∪ p.2)

theorem union_mem_families {N H L J : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N)
    {p : Finset ℕ × Finset ℕ} (hp : p ∈ pairs N H L J) :
    p.1 ∪ p.2 ∈ AlignedTripleExtensions.families PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L := by
  obtain ⟨hfactorial, hdis, hseed⟩ := mem_filter.mp hp
  obtain ⟨hbox, _hne⟩ := mem_filter.mp hfactorial
  obtain ⟨he, hf⟩ := mem_product.mp hbox
  have hsub := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (hsub he)
  obtain ⟨hfG, hfcard⟩ := mem_powersetCard.mp (hsub hf)
  have hcard : (p.1 ∪ p.2).card = 3 + 1 := by rw [card_union_of_disjoint hdis, hecard, hfcard]
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨union_subset heG hfG, hcard⟩, hseed⟩

theorem fibre_card {N H L J : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N)
    {T : Finset ℕ} (hT : T.card = 4) :
    ((pairs N H L J).filter fun p ↦ p.1 ∪ p.2 = T).card ≤ 36 := by
  have hsub : ((pairs N H L J).filter fun p ↦ p.1 ∪ p.2 = T) ⊆ T.powersetCard 2 ×ˢ T.powersetCard 2 := by
    intro p hp
    obtain ⟨hpp, hunion⟩ := mem_filter.mp hp
    obtain ⟨hfactorial, _hdis, _hseed⟩ := mem_filter.mp hpp
    obtain ⟨hbox, _hne⟩ := mem_filter.mp hfactorial
    obtain ⟨he, hf⟩ := mem_product.mp hbox
    have hall := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
    have heT : p.1 ⊆ T := by rw [← hunion]; exact subset_union_left
    have hfT : p.2 ⊆ T := by rw [← hunion]; exact subset_union_right
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨heT, (mem_powersetCard.mp (hall he)).2⟩,
      mem_powersetCard.mpr ⟨hfT, (mem_powersetCard.mp (hall hf)).2⟩⟩
  have hcard : (T.powersetCard 2).card = 6 := by rw [card_powersetCard, hT]; decide
  simpa only [card_product, hcard] using card_le_card hsub

theorem contribution_le_mass {N H L J : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    contribution N H L J ≤ 36 * AlignedTripleExtensions.mass PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L := by
  have hmap : (pairs N H L J : Set (Finset ℕ × Finset ℕ)).MapsTo
      (fun p ↦ p.1 ∪ p.2) (AlignedTripleExtensions.families PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L) :=
    fun _ hp ↦ union_mem_families hN hlarge hp
  calc
    _ = ∑ T ∈ AlignedTripleExtensions.families PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L,
        ∑ p ∈ (pairs N H L J).filter (fun p ↦ p.1 ∪ p.2 = T), infiniteJointMoment L (p.1 ∪ p.2) :=
      (sum_fiberwise_of_maps_to hmap (fun p ↦ infiniteJointMoment L (p.1 ∪ p.2))).symm
    _ = ∑ T ∈ AlignedTripleExtensions.families PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L,
        (((pairs N H L J).filter fun p ↦ p.1 ∪ p.2 = T).card : ℝ) * infiniteJointMoment L T := by
      apply sum_congr rfl
      intro T _
      calc
        _ = ∑ _p ∈ (pairs N H L J).filter (fun p ↦ p.1 ∪ p.2 = T), infiniteJointMoment L T :=
          sum_congr rfl (fun p hp ↦ congrArg (infiniteJointMoment L) (mem_filter.mp hp).2)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ T ∈ AlignedTripleExtensions.families PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L,
        36 * infiniteJointMoment L T := by
      apply sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast fibre_card hN hlarge (AlignedTripleExtensions.family_data hT).2.1)
        (infiniteJointMoment_nonneg L T)
    _ = _ := by rw [AlignedTripleExtensions.mass, mul_sum]

theorem contribution_nonneg (N H L J : ℕ) : 0 ≤ contribution N H L J :=
  sum_nonneg (fun p _ ↦ infiniteJointMoment_nonneg L (p.1 ∪ p.2))

end PaperP1.AlignedPrincipalEdgePairs
