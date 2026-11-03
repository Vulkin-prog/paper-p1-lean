module

public import PaperP1.Model.VariableRelationCore
public import PaperP1.Combinatorics.SeedComplementMass

/-! # All high compatible-nullity activities in the literal linear size range are covered by positive t-cores and free complements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HighNullityCoreCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

def cores (G : Finset ℕ) (t L : ℕ) (η : ℝ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun D ↦ Core t L D ∧ 0 < infiniteJointMoment L D ∧
    (L : ℝ) / 2 < runRelativeNullity L D ∧ (runRelativeNullity L D : ℝ) ≤ η * L

theorem mem_cores (G D : Finset ℕ) (t L : ℕ) (η : ℝ) :
    D ∈ cores G t L η ↔ D ⊆ G ∧ Core t L D ∧ 0 < infiniteJointMoment L D ∧
      (L : ℝ) / 2 < runRelativeNullity L D ∧ (runRelativeNullity L D : ℝ) ≤ η * L := by
  classical
  simp only [cores, mem_filter, mem_powerset]

theorem finite_bound (G : Finset ℕ) (t L K : ℕ) (η u : ℝ) (ht : 2 ≤ t) (hL : 0 < L)
    (hK : 2 * (t - 2) * K ≤ L) (hu : 0 ≤ u) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.card ≤ K ∧ (L : ℝ) < runCompatibleNullity L I ∧
      (runCompatibleNullity L I : ℝ) ≤ η * L) :
    (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
      Real.exp (∑ x ∈ G, ((2 : ℝ) ^ (t - 2 + 1) * u) * infiniteMarginal x L) *
        ∑ D ∈ cores G t L η, ((2 : ℝ) ^ (t - 2 + 1) * u) ^ D.card * infiniteJointMoment L D := by
  classical
  apply SeedComplementMass.cover_bound G F (cores G t L η)
    (fun x ↦ ((2 : ℝ) ^ (t - 2 + 1) * u) * infiniteMarginal x L)
    (fun D ↦ ((2 : ℝ) ^ (t - 2 + 1) * u) ^ D.card * infiniteJointMoment L D)
    (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  · intro x
    exact mul_nonneg (by positivity) (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  · intro D _hD
    exact mul_nonneg (pow_nonneg (by positivity) _) (infiniteJointMoment_nonneg L D)
  · intro D hD
    exact ((mem_cores G D t L η).mp hD).1
  · intro I hI
    obtain ⟨hIG, hsize, hhigh, hcap⟩ := hF I hI
    obtain ⟨D, hDI, hcore, hq, hupper, hbudget, hpeel⟩ := VariableRelationCore.exists_bound t L ht hL I
    have hcostNat : 2 * ((t - 2) * (I.card - D.card)) ≤ L := by
      calc
        _ ≤ 2 * ((t - 2) * K) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (t - 2)
          ((Nat.sub_le I.card D.card).trans hsize))
        _ = 2 * (t - 2) * K := by ring
        _ ≤ _ := hK
    have hcost : (((t - 2) * (I.card - D.card) : ℕ) : ℝ) ≤ (L : ℝ) / 2 := by
      have h : 2 * (((t - 2) * (I.card - D.card) : ℕ) : ℝ) ≤ L := by exact_mod_cast hcostNat
      linarith only [h]
    have hbudgetR : (runCompatibleNullity L I : ℝ) ≤ runRelativeNullity L D +
        (((t - 2) * (I.card - D.card) : ℕ) : ℝ) := by exact_mod_cast hbudget
    have hhighD : (L : ℝ) / 2 < runRelativeNullity L D := by linarith only [hhigh, hbudgetR, hcost]
    have hcapD : (runRelativeNullity L D : ℝ) ≤ η * L := by
      have hu : (runRelativeNullity L D : ℝ) ≤ runCompatibleNullity L I := by exact_mod_cast hupper
      exact hu.trans hcap
    exact ⟨hIG, D, (mem_cores G D t L η).mpr ⟨hDI.trans hIG, hcore, hq, hhighD, hcapD⟩,
      hDI, VariableRelationCore.weighted_bound (t - 2) L I D hDI hpeel u hu⟩

end PaperP1.HighNullityCoreCover
