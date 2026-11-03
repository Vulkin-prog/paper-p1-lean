module

public import PaperP1.Model.RelationCoreActivityPeeling

/-! # Compatible peeling cores for every prescribed projection threshold, retaining the actual rank and centered weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VariableRelationCore

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

theorem exists_bound (t L : ℕ) (ht : 2 ≤ t) (hL : 0 < L) (I : Finset ℕ) :
    ∃ D ⊆ I, Core t L D ∧ 0 < infiniteJointMoment L D ∧
      runRelativeNullity L D ≤ runCompatibleNullity L I ∧
      runCompatibleNullity L I ≤ runRelativeNullity L D + (t - 2) * (I.card - D.card) ∧
      |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
        (2 ^ ((t - 2) * (I.card - D.card)) : ℝ) *
        (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D := by
  obtain ⟨A, hAI, hqA, hmax⟩ := runCompatibleNullity_attained L I
  obtain ⟨D, htrace, hstop⟩ := RelationCorePeeling.exists_terminal_trace
    (fun x ↦ squareClassSpace x L) A (t - 2)
  have hDA := RelationCorePeeling.trace_subset _ htrace
  have hDI := hDA.trans hAI
  have hbudget := RelationCorePeeling.trace_nullity_budget _ htrace
  have hcost := Nat.mul_le_mul_left (t - 2) (Nat.sub_le_sub_right (card_le_card hAI) D.card)
  refine ⟨D, hDI, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hstop x hx
    omega
  · exact hqA.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L hDA)
  · rw [hmax]
    exact runRelativeNullity_mono L hDA
  · change runRelativeNullity L A ≤ runRelativeNullity L D + (t - 2) * (A.card - D.card) at hbudget
    rw [hmax]
    omega
  · exact RelationCoreActivityPeeling.peeling_bound L hL I A D (t - 2) hAI hqA hmax htrace

theorem weighted_bound (k L : ℕ) (I D : Finset ℕ) (hDI : D ⊆ I)
    (hpeel : |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
      (2 ^ (k * (I.card - D.card)) : ℝ) *
      (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D)
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ I.card * |infiniteCenteredCoefficient L I| ≤
      ((2 : ℝ) ^ (k + 1) * u) ^ D.card * infiniteJointMoment L D *
        ∏ x ∈ I \ D, ((2 : ℝ) ^ (k + 1) * u) * infiniteMarginal x L := by
  have hconst : (2 ^ I.card : ℝ) * 2 ^ (k * (I.card - D.card)) ≤
      ((2 : ℝ) ^ (k + 1)) ^ I.card := by
    rw [← pow_add, ← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    have hcost := Nat.mul_le_mul_left k (Nat.sub_le I.card D.card)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hnonneg : 0 ≤ u ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D :=
    mul_nonneg (mul_nonneg (pow_nonneg hu _)
      (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)) (infiniteJointMoment_nonneg L D)
  calc
    _ ≤ u ^ I.card * ((2 ^ I.card : ℝ) * 2 ^ (k * (I.card - D.card)) *
        (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D) :=
      mul_le_mul_of_nonneg_left hpeel (pow_nonneg hu _)
    _ = ((2 ^ I.card : ℝ) * 2 ^ (k * (I.card - D.card))) *
        (u ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D) := by ring
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ I.card *
        (u ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D) :=
      mul_le_mul_of_nonneg_right hconst hnonneg
    _ = ((2 : ℝ) ^ (k + 1) * u) ^ I.card *
        (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D := by rw [mul_pow]; ring
    _ = _ := by
      rw [prod_mul_distrib, prod_const, card_sdiff_of_subset hDI]
      have hcard : I.card = D.card + (I.card - D.card) := (Nat.add_sub_of_le (card_le_card hDI)).symm
      change ((2 : ℝ) ^ (k + 1) * u) ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D =
        ((2 : ℝ) ^ (k + 1) * u) ^ D.card * infiniteJointMoment L D *
          (((2 : ℝ) ^ (k + 1) * u) ^ (I.card - D.card) * ∏ x ∈ I \ D, infiniteMarginal x L)
      conv_lhs => rw [hcard, pow_add]
      ring

end PaperP1.VariableRelationCore
