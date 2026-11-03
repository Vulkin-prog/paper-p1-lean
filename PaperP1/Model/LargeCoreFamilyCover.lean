module

public import PaperP1.Model.ChosenRelationCore
public import PaperP1.Model.WeightedPrimitiveMass

/-! # Large compatible peeling cores cover actual activities at every cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeCoreFamilyCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

def cores (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun D ↦ 256 ≤ D.card ∧ Core 10 L D ∧ runRelativeNullity L D ≤ 2 * L

theorem mem_cores (G D : Finset ℕ) (L : ℕ) :
    D ∈ cores G L ↔ D ⊆ G ∧ 256 ≤ D.card ∧ Core 10 L D ∧ runRelativeNullity L D ≤ 2 * L := by
  classical
  simp only [cores, mem_filter, mem_powerset]

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ 256 ≤ (PaperP1.ChosenRelationCore.core L I).card ∧
      runCompatibleNullity L I ≤ 2 * L) :
    (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
      Real.exp (∑ x ∈ G, (512 * u) * infiniteMarginal x L) *
        ∑ D ∈ cores G L, (512 * u) ^ D.card * infiniteJointMoment L D := by
  classical
  apply PaperP1.SeedComplementMass.cover_bound G F (cores G L)
    (fun x ↦ (512 * u) * infiniteMarginal x L)
    (fun D ↦ (512 * u) ^ D.card * infiniteJointMoment L D)
    (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  · intro x
    exact mul_nonneg (by positivity) (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  · intro D _hD
    exact mul_nonneg (pow_nonneg (by positivity) _) (infiniteJointMoment_nonneg L D)
  · intro D hD
    exact ((mem_cores G D L).mp hD).1
  · intro I hI
    obtain ⟨hIG, hsize, hcap⟩ := hF I hI
    have hp := PaperP1.ChosenRelationCore.properties L hL I
    let D := PaperP1.ChosenRelationCore.core L I
    have hrank : runRelativeNullity L D ≤ runCompatibleNullity L I :=
      relativeNullityOn_le_compatibleNullityOn (fun x ↦ squareClassSpace x L)
        (infiniteJointMoment L) hp.1 hp.2.2.1
    refine ⟨hIG, D, (mem_cores G D L).mpr ⟨hp.1.trans hIG, hsize, hp.2.1, hrank.trans hcap⟩,
      hp.1, ?_⟩
    exact PaperP1.ChosenRelationCore.weighted_bound L hL I u hu

theorem source_mass_le_actual (G : Finset ℕ) (L : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    (∑ D ∈ cores G L, v ^ D.card * infiniteJointMoment L D) ≤
      PaperP1.WeightedPrimitiveMass.actualMass (cores G L) L v := by
  apply sum_le_sum
  intro D _hD
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (abs_nonneg (infiniteCenteredCoefficient L D))) (pow_nonneg hv _)

end PaperP1.LargeCoreFamilyCover
