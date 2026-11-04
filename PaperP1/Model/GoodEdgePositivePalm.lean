module

public import PaperP1.Model.SourceConditionalDeviations
public import PaperP1.Model.CompatibleChannelEdges
public import PaperP1.Model.PositivePairSeparation
public import PaperP1.Asymptotics.HomogeneousGoodPairExtensionsUnderInputs

/-! # Actual positive conditional source costs are bounded by homogeneous crossing seeds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgePositivePalm

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SourceConditionalDeviations

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def excess (L : ℕ) (e : Finset ℕ) (z : ℕ) : ℝ :=
  max 0 (infiniteJointMoment L (insert z e) - (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L e)

def points (N H a b L : ℕ) (G : Finset ℕ) : Finset (Finset ℕ × ℕ) :=
  ((CompatibleChannelEdges.edges N H a b L) ×ˢ G).filter fun p ↦ p.2 ∉ p.1

def mass (N H a b L : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ p ∈ points N H a b L G, infiniteJointMoment L p.1 *
    max 0 (conditionalStart p.1 L p.2 - (2 ^ L : ℝ)⁻¹)

def beta (N H a b L : ℕ) : ℝ :=
  ∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e

def normalized (N H a b L : ℕ) (G : Finset ℕ) : ℝ := mass N H a b L G / beta N H a b L

theorem scaled_positive_part (L : ℕ) (e : Finset ℕ) (z : ℕ) (hq : 0 < infiniteJointMoment L e) :
    infiniteJointMoment L e * max 0 (conditionalStart e L z - (2 ^ L : ℝ)⁻¹) = excess L e z := by
  rw [mul_max_of_nonneg _ _ hq.le, mul_zero]
  congr 1
  unfold conditionalStart
  field_simp

theorem iterated_mass (N H a b L : ℕ) (G : Finset ℕ) :
    mass N H a b L G = ∑ e ∈ CompatibleChannelEdges.edges N H a b L,
      infiniteJointMoment L e * ∑ z ∈ G \ e,
        max 0 (conditionalStart e L z - (2 ^ L : ℝ)⁻¹) := by
  unfold mass points
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro e _
  rw [sdiff_eq_filter, sum_filter, mul_sum]
  apply sum_congr rfl
  intro z _
  by_cases hz : z ∈ e <;> simp [hz]

theorem mass_eq_excess_sum (N H a b L : ℕ) (G : Finset ℕ) :
    mass N H a b L G = ∑ p ∈ points N H a b L G, excess L p.1 p.2 := by
  apply sum_congr rfl
  intro p hp
  exact scaled_positive_part L p.1 p.2 (mem_filter.mp (mem_product.mp (mem_filter.mp hp).1).1).2

theorem separated_of_positive_joint (L : ℕ) (hL : 0 < L) (T : Finset ℕ)
    (hq : 0 < infiniteJointMoment L T) : SeparatedHomogeneousMass.Separated L T := by
  intro x hx y hy hxy
  have hpair : ({x, y} : Finset ℕ) ⊆ T := insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩
  have hqpair := hq.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L hpair)
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · exact Or.inl (PositivePairSeparation.of_joint hL hxy hqpair)
  · exact Or.inr (PositivePairSeparation.of_joint hL hyx (by simpa only [pair_comm x y] using hqpair))

theorem positive_crossing {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (e : Finset ℕ) (z : ℕ)
    (hz : z ∈ RegularStarts.regularStarts N L) (hfresh : z ∉ e) (he : 0 < excess L e z) :
    0 < OneTargetCrossing.rank e L z := by
  have hpos : (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L e < infiniteJointMoment L (insert z e) := by
    have hh := (lt_max_iff.mp he).resolve_left (lt_irrefl 0)
    linarith only [hh]
  have hzpos : 0 < z := by
    have hh := (mem_Ico.mp (RegularStarts.regularStarts_subset N L hz)).1
    omega
  have hup := OneTargetCrossing.joint_upper e L z hL hfresh
  rw [RegularStarts.marginal_on_regular hzpos hL hz] at hup
  by_contra hn
  have hzero : OneTargetCrossing.rank e L z = 0 := by omega
  rw [hzero, pow_zero, mul_one] at hup
  linarith only [hup, hpos]

theorem positive_points_subset {N H a b L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ RegularStarts.regularStarts N L) :
    (points N H a b L G).filter (fun p ↦ 0 < excess L p.1 p.2) ⊆
      HomogeneousGoodPairExtensionsUnderInputs.points N H a b L := by
  intro p hp
  obtain ⟨hpp, hpos⟩ := mem_filter.mp hp
  obtain ⟨hbox, hfresh⟩ := mem_filter.mp hpp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  have hqpos : 0 < infiniteJointMoment L (insert p.2 p.1) := by
    have hh := (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
    have hn : 0 ≤ (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L p.1 := by
      exact mul_nonneg (by positivity) (infiniteJointMoment_nonneg L p.1)
    linarith only [hh, hn]
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨(mem_filter.mp he).1, hG hz⟩, hfresh, ?_, positive_crossing hN hL p.1 p.2 (hG hz) hfresh hpos⟩
  simpa only [SingletonExtensionWeights.join, union_singleton] using
    separated_of_positive_joint L hL (insert p.2 p.1) hqpos

theorem finite_mass {N H a b L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ RegularStarts.regularStarts N L) :
    mass N H a b L G ≤ HomogeneousGoodPairExtensionsUnderInputs.mass N H a b L := by
  let P := (points N H a b L G).filter fun p ↦ 0 < excess L p.1 p.2
  have heq : mass N H a b L G = ∑ p ∈ P, excess L p.1 p.2 := by
    rw [mass_eq_excess_sum]
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro p hp hnot
    have hn : ¬0 < excess L p.1 p.2 := fun h ↦ hnot (mem_filter.mpr ⟨hp, h⟩)
    exact le_antisymm (not_lt.mp hn) (le_max_left _ _)
  rw [heq]
  calc
    _ ≤ ∑ p ∈ P, HomogeneousRunMass.probability L (SingletonExtensionWeights.join p) := by
      apply sum_le_sum
      intro p _
      apply max_le (HomogeneousRunMass.probability_pos L _).le
      have hbound := HomogeneousRunMass.actual_joint_le L hL (insert p.2 p.1)
      have hn : 0 ≤ (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L p.1 :=
        mul_nonneg (by positivity) (infiniteJointMoment_nonneg L p.1)
      simpa only [SingletonExtensionWeights.join, union_singleton] using (sub_le_self _ hn).trans hbound
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (positive_points_subset hN hL hG)
      (fun p _ _ ↦ (HomogeneousRunMass.probability_pos L _).le)

theorem normalized_eq_iterated (N H a b L : ℕ) (G : Finset ℕ) :
    normalized N H a b L G = (1 / beta N H a b L) *
      ∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e *
        ∑ z ∈ G \ e, max 0 (conditionalStart e L z - (2 ^ L : ℝ)⁻¹) := by
  rw [normalized, iterated_mass, div_eq_mul_inv, one_div, mul_comm]

end PaperP1.GoodEdgePositivePalm
