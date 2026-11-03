module

public import PaperP1.Model.ChosenRelationCore
public import PaperP1.Model.SmallCoreRankRetention
public import PaperP1.Model.ConnectedComplementDeficit
public import PaperP1.Combinatorics.RestrictedSeedComplements

/-! # Small chosen compatible cores charge their exact non-direct independent complements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCoreFamilyCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.RelationCoreWitnesses PaperP1.ConnectedWindowFamilies

def cores (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun D ↦
    2 ≤ D.card ∧ D.card < 256 ∧ Core 10 L D ∧ 0 < infiniteJointMoment L D

def sourceMass (G : Finset ℕ) (L : ℕ) (v : ℝ) : ℝ :=
  ∑ D ∈ cores G L, v ^ D.card * infiniteJointMoment L D *
    PaperP1.IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L v

theorem mem_cores (G D : Finset ℕ) (L : ℕ) :
    D ∈ cores G L ↔ D ⊆ G ∧ 2 ≤ D.card ∧ D.card < 256 ∧ Core 10 L D ∧
      0 < infiniteJointMoment L D := by
  classical
  simp only [cores, mem_filter, mem_powerset]

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ Connected L I ∧ 256 < I.card ∧
      2 ≤ (PaperP1.ChosenRelationCore.core L I).card ∧
      (PaperP1.ChosenRelationCore.core L I).card < 256) :
    (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ sourceMass G L (512 * u) := by
  classical
  unfold sourceMass
  simp_rw [PaperP1.IndependentExtensionDeficit.deficit_eq_product_weights]
  apply PaperP1.RestrictedSeedComplements.cover_bound F (cores G L)
    (fun D ↦ PaperP1.IndependentExtensionDeficit.families (G \ D)
      (span (fun x ↦ squareClassSpace x L) D) L)
    (fun x ↦ (512 * u) * infiniteMarginal x L)
    (fun D ↦ (512 * u) ^ D.card * infiniteJointMoment L D)
    (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  · intro x
    exact mul_nonneg (by positivity) (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  · intro D _hD
    exact mul_nonneg (pow_nonneg (by positivity) _) (infiniteJointMoment_nonneg L D)
  · intro I hI
    obtain ⟨hIG, hconn, hlarge, htwo, hsmall⟩ := hF I hI
    let D := PaperP1.ChosenRelationCore.core L I
    change 2 ≤ D.card at htwo
    change D.card < 256 at hsmall
    have hp := PaperP1.ChosenRelationCore.properties L hL I
    have hproper : D ⊂ I := by
      apply ssubset_iff_subset_ne.mpr
      refine ⟨hp.1, ?_⟩
      intro heq
      have hcard := congrArg Finset.card heq
      omega
    refine ⟨D, (mem_cores G D L).mpr ⟨hp.1.trans hIG, htwo, hsmall, hp.2.1, hp.2.2.1⟩,
      hp.1, ?_, PaperP1.ChosenRelationCore.weighted_bound L hL I u hu⟩
    exact PaperP1.ConnectedComplementDeficit.complement_mem G L I D hIG hproper
      (card_pos.mp (by omega)) hconn

theorem centered_source_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (v : ℝ) (hv : 0 ≤ v) :
    sourceMass G L v ≤ 2 * ∑ D ∈ cores G L, v ^ D.card * |infiniteCenteredCoefficient L D| *
      PaperP1.IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L v := by
  rw [mul_sum]
  apply sum_le_sum
  intro D hD
  obtain ⟨_hDG, _htwo, hsmall, hcore, hq⟩ := (mem_cores G D L).mp hD
  have hratio : infiniteJointMoment L D ≤ 2 * |infiniteCenteredCoefficient L D| :=
    (PaperP1.RelationCoreMomentRatio.ten_core_ratio L D hL hq (by omega) hcore).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
  have hE : 0 ≤ PaperP1.IndependentExtensionDeficit.deficit
      G D (span (fun x ↦ squareClassSpace x L) D) L v :=
    sum_nonneg fun U _ ↦ mul_nonneg (pow_nonneg hv _)
      (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (pow_nonneg hv D.card)) hE
  exact h.trans_eq (by ring)

end PaperP1.SmallCoreFamilyCover
