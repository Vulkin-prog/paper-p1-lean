module

public import PaperP1.Model.RelationCoreActivityPeeling
public import PaperP1.Combinatorics.SeedComplementMass

/-! # A chosen actual compatible relation core and independently weighted complements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChosenRelationCore

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts PaperP1.RelationCoreWitnesses

def core (L : ℕ) (I : Finset ℕ) : Finset ℕ :=
  if hL : 0 < L then Classical.choose (PaperP1.RelationCoreActivityPeeling.exists_ten_core_bound L hL I)
  else ∅

theorem properties (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    core L I ⊆ I ∧ Core 10 L (core L I) ∧ 0 < infiniteJointMoment L (core L I) ∧
      runCompatibleNullity L I ≤ runRelativeNullity L (core L I) + 8 * (I.card - (core L I).card) ∧
      |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
        (2 ^ (8 * (I.card - (core L I).card)) : ℝ) *
        (∏ x ∈ I \ core L I, infiniteMarginal x L) * infiniteJointMoment L (core L I) := by
  unfold core
  rw [dite_eq_left hL]
  exact Classical.choose_spec (PaperP1.RelationCoreActivityPeeling.exists_ten_core_bound L hL I)

theorem weighted_bound (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (u : ℝ) (hu : 0 ≤ u) :
    u ^ I.card * |infiniteCenteredCoefficient L I| ≤
      (512 * u) ^ (core L I).card * infiniteJointMoment L (core L I) *
        ∏ x ∈ I \ core L I, (512 * u) * infiniteMarginal x L := by
  have h := properties L hL I
  let D := core L I
  have hDI : D ⊆ I := h.1
  have hqD : 0 ≤ infiniteJointMoment L D := h.2.2.1.le
  have hpeel := h.2.2.2.2
  have hconst : (2 ^ I.card : ℝ) * 2 ^ (8 * (I.card - D.card)) ≤ (512 : ℝ) ^ I.card := by
    rw [← pow_add]
    calc
      _ ≤ (2 : ℝ) ^ (9 * I.card) := pow_le_pow_right₀ (by norm_num)
        (by have hsub := Nat.sub_le I.card D.card; omega)
      _ = _ := by rw [pow_mul]; norm_num
  have hnonneg : 0 ≤ u ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D :=
    mul_nonneg (mul_nonneg (pow_nonneg hu _)
      (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)) hqD
  calc
    _ ≤ u ^ I.card * ((2 ^ I.card : ℝ) * 2 ^ (8 * (I.card - D.card)) *
        (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D) :=
      mul_le_mul_of_nonneg_left hpeel (pow_nonneg hu _)
    _ = ((2 ^ I.card : ℝ) * 2 ^ (8 * (I.card - D.card))) *
        (u ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D) := by ring
    _ ≤ (512 : ℝ) ^ I.card *
        (u ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D) :=
      mul_le_mul_of_nonneg_right hconst hnonneg
    _ = (512 * u) ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [prod_mul_distrib, prod_const, card_sdiff_of_subset hDI]
      have hcard : I.card = D.card + (I.card - D.card) := (Nat.add_sub_of_le (card_le_card hDI)).symm
      change (512 * u) ^ I.card * (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D =
        (512 * u) ^ D.card * infiniteJointMoment L D *
          ((512 * u) ^ (I.card - D.card) * ∏ x ∈ I \ D, infiniteMarginal x L)
      conv_lhs => rw [hcard, pow_add]
      ring

end PaperP1.ChosenRelationCore
