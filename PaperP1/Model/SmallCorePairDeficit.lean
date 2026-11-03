module

public import PaperP1.Model.SmallCoreFamilyCover
public import PaperP1.Model.AllPairDeficitMonotonicity

/-! # Size-two small cores retain the full weighted pair deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCorePairDeficit

open Finset PaperP1.Arithmetic PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.SmallCoreFamilyCover

theorem source_split (G : Finset ℕ) (L : ℕ) (v : ℝ) :
    sourceMass G L v =
      (∑ D ∈ (cores G L).filter (fun D ↦ D.card = 2), v ^ D.card * infiniteJointMoment L D *
        IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L v) +
      ∑ D ∈ (cores G L).filter (fun D ↦ 3 ≤ D.card), v ^ D.card * infiniteJointMoment L D *
        IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L v := by
  classical
  rw [sourceMass, ← sum_filter_add_sum_filter_not (cores G L) (fun D ↦ D.card = 2)]
  congr 1
  apply sum_congr
  · ext D
    simp only [mem_filter]
    constructor
    · rintro ⟨hD, hn⟩
      have ht := ((mem_cores G D L).mp hD).2.1
      exact ⟨hD, by omega⟩
    · rintro ⟨hD, hh⟩
      exact ⟨hD, by omega⟩
  · intro D _
    rfl

theorem pair_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (v : ℝ) (hv : 0 ≤ v) :
    (∑ D ∈ (cores G L).filter (fun D ↦ D.card = 2), v ^ D.card * infiniteJointMoment L D *
      IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L v) ≤
        2 * v ^ 2 * AllPairExtensionDeficit.deficit G L v := by
  classical
  let T := (cores G L).filter (fun D ↦ D.card = 2)
  calc
    _ ≤ ∑ D ∈ T, (2 * v ^ 2) * (|infiniteCenteredCoefficient L D| *
        IndependentExtensionDeficit.deficit G D (FixedPairExtensions.sourceSpace D L) L v) := by
      apply sum_le_sum
      intro D hD
      obtain ⟨hDc, hcard⟩ := mem_filter.mp hD
      obtain ⟨_hDG, _htwo, hsmall, hcore, hq⟩ := (mem_cores G D L).mp hDc
      have hratio : infiniteJointMoment L D ≤ 2 * |infiniteCenteredCoefficient L D| :=
        (RelationCoreMomentRatio.ten_core_ratio L D hL hq (by omega) hcore).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
      have he := IndependentDeficitMonotonicity.nonneg G D
        (FixedPairExtensions.sourceSpace D L) L v hv
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (pow_nonneg hv 2)) he
      simpa only [hcard, FixedPairExtensions.sourceSpace, mul_assoc, mul_left_comm, mul_comm] using h
    _ = (2 * v ^ 2) * ∑ D ∈ T, |infiniteCenteredCoefficient L D| *
        IndependentExtensionDeficit.deficit G D (FixedPairExtensions.sourceSpace D L) L v := by
      rw [mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro D hD
        obtain ⟨hDc, hcard⟩ := mem_filter.mp hD
        exact mem_powersetCard.mpr ⟨((mem_cores G D L).mp hDc).1, hcard⟩
      · intro D _ _
        exact mul_nonneg (abs_nonneg _) (IndependentDeficitMonotonicity.nonneg G D _ L v hv)

theorem pair_family_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ ConnectedWindowFamilies.Connected L I ∧ 256 < I.card ∧
      (ChosenRelationCore.core L I).card = 2) :
    (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
      2 * (512 * u) ^ 2 * AllPairExtensionDeficit.deficit G L (512 * u) := by
  classical
  apply le_trans _ (pair_bound G L hL (512 * u) (by positivity))
  simp_rw [IndependentExtensionDeficit.deficit_eq_product_weights]
  apply RestrictedSeedComplements.cover_bound F
    ((cores G L).filter (fun D ↦ D.card = 2))
    (fun D ↦ IndependentExtensionDeficit.families (G \ D)
      (span (fun x ↦ squareClassSpace x L) D) L)
    (fun x ↦ (512 * u) * infiniteMarginal x L)
    (fun D ↦ (512 * u) ^ D.card * infiniteJointMoment L D)
    (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  · intro x
    exact mul_nonneg (by positivity) (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  · intro D _
    exact mul_nonneg (pow_nonneg (by positivity) _) (infiniteJointMoment_nonneg L D)
  · intro I hI
    obtain ⟨hIG, hconn, hlarge, hcard⟩ := hF I hI
    let D := ChosenRelationCore.core L I
    change D.card = 2 at hcard
    have hp := ChosenRelationCore.properties L hL I
    have hproper : D ⊂ I := by
      apply ssubset_iff_subset_ne.mpr
      refine ⟨hp.1, ?_⟩
      intro heq
      have hsize := congrArg Finset.card heq
      omega
    refine ⟨D, mem_filter.mpr ⟨(mem_cores G D L).mpr
      ⟨hp.1.trans hIG, by omega, by omega, hp.2.1, hp.2.2.1⟩, hcard⟩,
      hp.1, ?_, ChosenRelationCore.weighted_bound L hL I u hu⟩
    exact ConnectedComplementDeficit.complement_mem G L I D hIG hproper
      (card_pos.mp (by omega)) hconn

end PaperP1.SmallCorePairDeficit
