module

public import PaperP1.Model.GoodEdgePositivePalm
public import PaperP1.Asymptotics.HomogeneousEffectiveGoodPairExtensions

/-! # Exact and nominal positive Palm costs on every original target window

The exact excess is centered at the actual target marginal. Its positive
support forces a separated triple and a nonzero effective crossing, without
requiring regularity or dividing by the target marginal. Nominal recentering
costs only the total marginal discrepancy times the compatible source mass.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.AllTargetGoodEdgePalm

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def exactExcess (L : ℕ) (e : Finset ℕ) (z : ℕ) : ℝ :=
  max 0 (infiniteJointMoment L (insert z e) - infiniteJointMoment L e * infiniteMarginal z L)

def exactMass (N H a b L : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ p ∈ GoodEdgePositivePalm.points N H a b L G, exactExcess L p.1 p.2

def combinedMass (N H a b L : ℕ) (G : Finset ℕ) : ℝ :=
  exactMass N H a b L G + GoodEdgePositivePalm.mass N H a b L G

def normalized (N H a b L : ℕ) (G : Finset ℕ) : ℝ :=
  combinedMass N H a b L G / GoodEdgePositivePalm.beta N H a b L

def marginalError (N L : ℕ) : ℝ :=
  ∑ z ∈ dyadicBlock N, |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹|

theorem exactExcess_nonneg (L : ℕ) (e : Finset ℕ) (z : ℕ) : 0 ≤ exactExcess L e z :=
  le_max_left _ _

theorem exactMass_nonneg (N H a b L : ℕ) (G : Finset ℕ) : 0 ≤ exactMass N H a b L G :=
  sum_nonneg fun p _ ↦ exactExcess_nonneg L p.1 p.2

theorem positive_crossing {L : ℕ} (hL : 0 < L) (e : Finset ℕ) (z : ℕ)
    (hfresh : z ∉ e) (he : 0 < exactExcess L e z) : 0 < OneTargetCrossing.rank e L z := by
  have hpos := (lt_max_iff.mp he).resolve_left (lt_irrefl 0)
  have hup := OneTargetCrossing.joint_upper e L z hL hfresh
  by_contra hn
  have hzero : OneTargetCrossing.rank e L z = 0 := by omega
  rw [hzero, pow_zero, mul_one] at hup
  linarith only [hpos, hup]

theorem positive_points_subset {N H a b L : ℕ} (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    (GoodEdgePositivePalm.points N H a b L G).filter (fun p ↦ 0 < exactExcess L p.1 p.2) ⊆
      HomogeneousEffectiveGoodPairExtensions.points N H a b L := by
  intro p hp
  obtain ⟨hpp, hpos⟩ := mem_filter.mp hp
  obtain ⟨hbox, hfresh⟩ := mem_filter.mp hpp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  have hqpos : 0 < infiniteJointMoment L (insert p.2 p.1) := by
    have hh := (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
    have hn := mul_nonneg (infiniteJointMoment_nonneg L p.1)
      (MissingBlockProbabilities.infiniteMarginal_nonneg p.2 L)
    linarith only [hh, hn]
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨(mem_filter.mp he).1, hG hz⟩, hfresh, ?_,
    positive_crossing hL p.1 p.2 hfresh hpos⟩
  simpa only [SingletonExtensionWeights.join, union_singleton] using
    GoodEdgePositivePalm.separated_of_positive_joint L hL (insert p.2 p.1) hqpos

theorem finite_exact_mass {N H a b L : ℕ} (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    exactMass N H a b L G ≤ HomogeneousEffectiveGoodPairExtensions.mass N H a b L := by
  let P := (GoodEdgePositivePalm.points N H a b L G).filter fun p ↦ 0 < exactExcess L p.1 p.2
  have heq : exactMass N H a b L G = ∑ p ∈ P, exactExcess L p.1 p.2 := by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro p hp hnot
    have hn : ¬0 < exactExcess L p.1 p.2 := fun h ↦ hnot (mem_filter.mpr ⟨hp, h⟩)
    exact le_antisymm (not_lt.mp hn) (exactExcess_nonneg _ _ _)
  rw [heq]
  calc
    _ ≤ ∑ p ∈ P, HomogeneousRunMass.probability L (SingletonExtensionWeights.join p) := by
      apply sum_le_sum
      intro p _
      apply max_le (HomogeneousRunMass.probability_pos L _).le
      have hbound := HomogeneousRunMass.actual_joint_le L hL (insert p.2 p.1)
      have hn := mul_nonneg (infiniteJointMoment_nonneg L p.1)
        (MissingBlockProbabilities.infiniteMarginal_nonneg p.2 L)
      simpa only [SingletonExtensionWeights.join, union_singleton] using (sub_le_self _ hn).trans hbound
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (positive_points_subset hL hG)
      (fun p _ _ ↦ (HomogeneousRunMass.probability_pos L _).le)

theorem nominal_recenter (L : ℕ) (e : Finset ℕ) (z : ℕ) :
    GoodEdgePositivePalm.excess L e z ≤ exactExcess L e z +
      infiniteJointMoment L e * |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹| := by
  have hq := infiniteJointMoment_nonneg L e
  have he : infiniteJointMoment L (insert z e) -
      infiniteJointMoment L e * infiniteMarginal z L ≤ exactExcess L e z := le_max_right _ _
  have ha := mul_le_mul_of_nonneg_left (le_abs_self (infiniteMarginal z L - (2 ^ L : ℝ)⁻¹)) hq
  apply max_le
  · exact add_nonneg (exactExcess_nonneg L e z) (mul_nonneg hq (abs_nonneg _))
  · change infiniteJointMoment L (insert z e) - (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L e ≤ _
    nlinarith only [he, ha]

theorem finite_nominal_mass {N H a b L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    GoodEdgePositivePalm.mass N H a b L G ≤ exactMass N H a b L G +
      GoodEdgePositivePalm.beta N H a b L * marginalError N L := by
  rw [GoodEdgePositivePalm.mass_eq_excess_sum]
  have hpoint := sum_le_sum (s := GoodEdgePositivePalm.points N H a b L G)
    (fun p _ ↦ nominal_recenter L p.1 p.2)
  rw [sum_add_distrib] at hpoint
  apply hpoint.trans
  apply add_le_add le_rfl
  have hsub : GoodEdgePositivePalm.points N H a b L G ⊆
      CompatibleChannelEdges.edges N H a b L ×ˢ dyadicBlock N := by
    intro p hp
    obtain ⟨he, hz⟩ := mem_product.mp (mem_filter.mp hp).1
    exact mem_product.mpr ⟨he, hG hz⟩
  calc
    _ ≤ ∑ p ∈ CompatibleChannelEdges.edges N H a b L ×ˢ dyadicBlock N,
        infiniteJointMoment L p.1 * |infiniteMarginal p.2 L - (2 ^ L : ℝ)⁻¹| :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦
        mul_nonneg (infiniteJointMoment_nonneg L p.1) (abs_nonneg _))
    _ = _ := by
      rw [sum_product]
      simp_rw [← mul_sum]
      rw [← sum_mul]
      rfl

theorem nominal_normalized_le (N H a b L : ℕ) (G : Finset ℕ) :
    GoodEdgePositivePalm.normalized N H a b L G ≤ normalized N H a b L G := by
  apply div_le_div_of_nonneg_right _ (sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L e)
  exact le_add_of_nonneg_left (exactMass_nonneg N H a b L G)

end PaperP1.AllTargetGoodEdgePalm
