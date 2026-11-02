module

public import PaperP1.Model.PrivateChannelRank

/-! # The actual compatible dependent edge population of a fixed private channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleChannelEdges

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateChannelSources
  PaperP1.PrivateChannelActivity

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def edges (N H a b L : ℕ) : Finset (Finset ℕ) :=
  (pairs N H a b L).filter fun e ↦ 0 < infiniteJointMoment L e

def independentMass (N H a b L : ℕ) : ℝ :=
  ∑ e ∈ edges N H a b L, ∏ x ∈ e, infiniteMarginal x L

theorem card_bound {N H a b L : ℕ} (hN : 0 < N) (ha : 0 < a) :
    (edges N H a b L).card ≤ (2 * (a + b) + 1) * (L + 1) * N :=
  (card_filter_le _ _).trans (card_bound_linear hN ha)

theorem edge_data {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L)
    {e : Finset ℕ} (he : e ∈ edges N H a b L) :
    e ⊆ RegularStarts.regularStarts N L ∧ e.card = 2 ∧
      0 < runRelativeNullity L e ∧ (runRelativeNullity L e : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b ∧
      0 < infiniteJointMoment L e ∧ infiniteJointMoment L e ≤
        ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  obtain ⟨he, hq⟩ := mem_filter.mp he
  exact ⟨PrivateChannelRank.regular hN ha hab he, (pair_data hN hab hlarge he).2,
    PrivateChannelRank.nullity_positive hN ha hab hlarge he,
    PrivateChannelRank.nullity_bound hN ha hab hcop hlarge he, hq,
    PrivateChannelRank.joint_bound hN ha hab hcop hlarge hL he⟩

theorem joint_mass_eq {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    (∑ e ∈ edges N H a b L, infiniteJointMoment L e) = channelMass N H a b L / 2 := by
  rw [← PrivateChannelActivity.joint_mass_eq hN hab hlarge, edges]
  apply sum_subset (filter_subset _ _)
  intro e _ he
  have hq : ¬0 < infiniteJointMoment L e := by
    intro hq
    exact he (mem_filter.mpr ⟨by assumption, hq⟩)
  exact le_antisymm (not_lt.mp hq) (infiniteJointMoment_nonneg L e)

theorem absolute_eq {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    CompatibleActivitySplit.absolute L (edges N H a b L) =
      channelMass N H a b L / 2 - independentMass N H a b L := by
  calc
    _ = ∑ e ∈ edges N H a b L, (infiniteJointMoment L e - ∏ x ∈ e, infiniteMarginal x L) := by
      apply sum_congr rfl
      intro e he
      obtain ⟨he, hq⟩ := mem_filter.mp he
      rw [abs_of_nonneg (CompatibleRunCentered.coefficient_nonneg L e hL hq)]
      exact CompressedJointMoments.centered_pair L e (pair_data hN hab hlarge he).2
    _ = _ := by rw [sum_sub_distrib, joint_mass_eq hN hab hlarge, independentMass]

theorem absolute_comparison {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    |CompatibleActivitySplit.absolute L (edges N H a b L) - channelMass N H a b L / 2| ≤
      PrivateChannelActivity.independentMass N H a b L := by
  rw [absolute_eq hN hab hlarge hL]
  have hi : 0 ≤ independentMass N H a b L := sum_nonneg fun e _ ↦
    prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hle : independentMass N H a b L ≤ PrivateChannelActivity.independentMass N H a b L :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun e _ _ ↦
      prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have heq : channelMass N H a b L / 2 - independentMass N H a b L - channelMass N H a b L / 2 =
      -independentMass N H a b L := by ring
  rw [heq, abs_neg, abs_of_nonneg hi]
  exact hle

end PaperP1.CompatibleChannelEdges
