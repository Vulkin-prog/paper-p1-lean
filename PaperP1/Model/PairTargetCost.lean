module

public import PaperP1.Model.WindowTargetHosts
public import PaperP1.Model.FiniteGoodChannelPartition
public import PaperP1.Arithmetic.CompressedChannelTargetHosts

/-! # Actual restricted pair/target costs, incidence, and the finite channel partition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairTargetCost

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DependentFamilySeeds
  PaperP1.IndependentTargetDeficit PaperP1.FiniteGoodChannelPartition

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def cost (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) : ℝ :=
  |infiniteCenteredCoefficient L e| * ∑ z ∈ WindowTargetHosts.targets G L e, infiniteMarginal z L

def mass (G : Finset ℕ) (L : ℕ) (F : Finset (Finset ℕ)) : ℝ := ∑ e ∈ F, cost G L e

def events (G : Finset ℕ) (L : ℕ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ × ℕ) :=
  (F ×ˢ G).filter fun p ↦ p.2 ∉ p.1 ∧ targetDependent L p.1 p.2

def eventKey (p : (ℕ × ℕ) × ℕ) : Finset ℕ × ℕ := ({p.1.1, p.1.2}, p.2)

theorem cost_nonneg (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) : 0 ≤ cost G L e :=
  mul_nonneg (abs_nonneg _) (sum_nonneg fun z _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg z L)

theorem mass_mono {G : Finset ℕ} {L : ℕ} {F H : Finset (Finset ℕ)} (hFH : F ⊆ H) :
    mass G L F ≤ mass G L H := sum_le_sum_of_subset_of_nonneg hFH (fun e _ _ ↦ cost_nonneg G L e)

theorem cost_ground_mono {G H : Finset ℕ} (hGH : G ⊆ H) (L : ℕ) (e : Finset ℕ) :
    cost G L e ≤ cost H L e := by
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply sum_le_sum_of_subset_of_nonneg
  · intro z hz
    obtain ⟨hzG, hdep⟩ := mem_filter.mp hz
    obtain ⟨hzG, hze⟩ := mem_sdiff.mp hzG
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hGH hzG, hze⟩, hdep⟩
  · exact fun z _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg z L

theorem mass_ground_mono {G H : Finset ℕ} (hGH : G ⊆ H) (L : ℕ) (F : Finset (Finset ℕ)) :
    mass G L F ≤ mass H L F := sum_le_sum (fun e _ ↦ cost_ground_mono hGH L e)

theorem deficit_eq (G : Finset ℕ) (L : ℕ) :
    deficit G L = mass G L (dependentFamilies G L 2) := by
  have hfilter : (G.powersetCard 2).filter (dependentPair L) = dependentFamilies G L 2 := by
    ext e
    constructor
    · intro he
      obtain ⟨heG, hp⟩ := mem_filter.mp he
      apply mem_filter.mpr
      exact ⟨heG, by simpa only [dependentPair, runRelativeNullity] using hp⟩
    · intro he
      obtain ⟨heG, hp⟩ := mem_filter.mp he
      apply mem_filter.mpr
      exact ⟨heG, by simpa only [dependentPair, runRelativeNullity] using hp⟩
  unfold deficit mass
  rw [hfilter]
  simp only [cost, WindowTargetHosts.targets]

theorem deficit_mono {G H : Finset ℕ} (hGH : G ⊆ H) (L : ℕ) : deficit G L ≤ deficit H L := by
  have hdep : dependentFamilies G L 2 ⊆ dependentFamilies H L 2 := by
    intro e he
    obtain ⟨heG, hpos⟩ := mem_filter.mp he
    obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp heG
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hesub.trans hGH, hecard⟩, hpos⟩
  rw [deficit_eq, deficit_eq]
  exact (mass_ground_mono hGH L _).trans (mass_mono hdep)

theorem mass_eq_events (G : Finset ℕ) (L : ℕ) (F : Finset (Finset ℕ)) :
    mass G L F = ∑ p ∈ events G L F, |infiniteCenteredCoefficient L p.1| * infiniteMarginal p.2 L := by
  unfold mass cost events
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro e _he
  have hfilter : WindowTargetHosts.targets G L e = G.filter (fun z ↦ z ∉ e ∧ targetDependent L e z) := by
    ext z
    simp only [WindowTargetHosts.targets, mem_filter, mem_sdiff]
    tauto
  rw [hfilter, sum_filter, mul_sum]
  apply sum_congr rfl
  intro z _hz
  split_ifs <;> simp only [mul_zero]

theorem private_events_cover (N H a b L : ℕ) :
    events (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L) ⊆
      (CompressedChannelTargetHosts.allTargets N a b L).image eventKey := by
  intro p hp
  rcases p with ⟨e, z⟩
  obtain ⟨hpG, _hze, hdep⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hpG
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, hu, _hprivate⟩ := PrivateChannelSources.mem_goodSources.mp hxy
  have hunit : (NormalizedUnitCount.units a b xy.1 xy.2 L).Nonempty := card_pos.mp (by omega)
  apply mem_image.mpr
  refine ⟨(xy, z), ?_, rfl⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hz⟩, hunit, hdep⟩

theorem private_events_card (N H a b L : ℕ) :
    (events (dyadicBlock N) L (PrivateChannelActivity.pairs N H a b L)).card ≤
      (CompressedChannelTargetHosts.allTargets N a b L).card :=
  (card_le_card (private_events_cover N H a b L)).trans card_image_le

theorem partition_formula (Q N H L : ℕ) :
    deficit (dyadicBlock N) L =
      mass (dyadicBlock N) L (good Q N H L) + mass (dyadicBlock N) L (weak Q N H L) +
        mass (dyadicBlock N) L (exceptional Q N H L) := by
  have hdis : Disjoint (good Q N H L ∪ weak Q N H L) (exceptional Q N H L) := by
    apply disjoint_left.mpr
    exact fun _ he hex ↦ (mem_sdiff.mp hex).2 he
  rw [deficit_eq, mass, ← cover Q N H L, sum_union hdis, sum_union (disjoint_classes Q N H L).1]
  rfl

end PaperP1.PairTargetCost
