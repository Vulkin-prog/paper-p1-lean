module

public import PaperP1.Model.JointBlockCovariance
public import PaperP1.Model.PrincipalSecondMomentReduction

/-! # A literal rank split of the residual principal-edge covariance population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalResidualDensity

open Finset PaperP1.Model.InfiniteStarts PaperP1.PrincipalEdgeSpaces PaperP1.JointBlockCovariance
  PaperP1.PrincipalSecondMomentReduction

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def boundedPairs (N H L : ℕ) (θ : ℝ) : Finset (Finset ℕ × Finset ℕ) :=
  (coupledPairs N H L).filter fun p ↦ (intersectionRank L p.1 p.2 : ℝ) ≤ θ * L

def boundedCovariance (N H L : ℕ) (θ : ℝ) : ℝ := ∑ p ∈ boundedPairs N H L θ,
  |infiniteJointMoment L (p.1 ∪ p.2) - infiniteJointMoment L p.1 * infiniteJointMoment L p.2|

def densePairs (N H L J : ℕ) (θ : ℝ) : Finset (Finset ℕ × Finset ℕ) :=
  (residualPairs N H L J).filter fun p ↦ θ * L < (intersectionRank L p.1 p.2 : ℝ)

def denseCovariance (N H L J : ℕ) (θ : ℝ) : ℝ := ∑ p ∈ densePairs N H L J θ,
  |infiniteJointMoment L (p.1 ∪ p.2) - infiniteJointMoment L p.1 * infiniteJointMoment L p.2|

theorem bounded_nonneg (N H L : ℕ) (θ : ℝ) : 0 ≤ boundedCovariance N H L θ :=
  sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem dense_nonneg (N H L J : ℕ) (θ : ℝ) : 0 ≤ denseCovariance N H L J θ :=
  sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem principal_positive {N H L : ℕ} {e : Finset ℕ} (he : e ∈ PrincipalChannelEdges.edges N H L) :
    0 < infiniteJointMoment L e := by
  rcases mem_union.mp he with he | he
  · exact (mem_filter.mp he).2
  · exact (mem_filter.mp he).2

theorem bounded_by_cap {N H L : ℕ} {θ M : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (hcap : ∀ p ∈ boundedPairs N H L θ, (2 ^ intersectionRank L p.1 p.2 : ℝ) ≤ M) :
    boundedCovariance N H L θ ≤ M * coupledProductMass N H L := by
  have hpoint (p : Finset ℕ × Finset ℕ) (hp : p ∈ boundedPairs N H L θ) :
      |infiniteJointMoment L (p.1 ∪ p.2) - infiniteJointMoment L p.1 * infiniteJointMoment L p.2| ≤
        M * (infiniteJointMoment L p.1 * infiniteJointMoment L p.2) := by
    have hbox := (mem_filter.mp (mem_filter.mp hp).1).1
    obtain ⟨he, hf⟩ := mem_product.mp hbox
    exact (actual_covariance_bound L hL p.1 p.2 (principal_positive he) (principal_positive hf)).trans
      (mul_le_mul_of_nonneg_right (hcap p hp) (mul_nonneg (infiniteJointMoment_nonneg L p.1) (infiniteJointMoment_nonneg L p.2)))
  calc
    _ ≤ ∑ p ∈ boundedPairs N H L θ, M * (infiniteJointMoment L p.1 * infiniteJointMoment L p.2) := sum_le_sum hpoint
    _ = M * ∑ p ∈ boundedPairs N H L θ, infiniteJointMoment L p.1 * infiniteJointMoment L p.2 := by rw [mul_sum]
    _ ≤ M * ∑ p ∈ coupledPairs N H L, infiniteJointMoment L p.1 * infiniteJointMoment L p.2 :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun p _ _ ↦ mul_nonneg (infiniteJointMoment_nonneg L p.1) (infiniteJointMoment_nonneg L p.2))) hM
    _ = _ := rfl

theorem dense_le_residual (N H L J : ℕ) (θ : ℝ) :
    denseCovariance N H L J θ ≤ residualCovariance N H L J :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ abs_nonneg _)

theorem residual_le_bounded_add_dense (N H L J : ℕ) (θ : ℝ) :
    residualCovariance N H L J ≤ boundedCovariance N H L θ + denseCovariance N H L J θ := by
  let w := fun p : Finset ℕ × Finset ℕ ↦
    |infiniteJointMoment L (p.1 ∪ p.2) - infiniteJointMoment L p.1 * infiniteJointMoment L p.2|
  let low := (residualPairs N H L J).filter fun p ↦ (intersectionRank L p.1 p.2 : ℝ) ≤ θ * L
  have hsub : low ⊆ boundedPairs N H L θ := by
    intro p hp
    obtain ⟨hpR, hcap⟩ := mem_filter.mp hp
    obtain ⟨hfactorial, _hset, _hseed, hspaces⟩ := mem_filter.mp hpR
    have hbox := (mem_filter.mp hfactorial).1
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hbox, hspaces⟩, hcap⟩
  have hlow : (∑ p ∈ low, w p) ≤ boundedCovariance N H L θ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ abs_nonneg _)
  have hsplit := sum_filter_add_sum_filter_not (residualPairs N H L J)
    (fun p ↦ (intersectionRank L p.1 p.2 : ℝ) ≤ θ * L) w
  have hhigh : ((residualPairs N H L J).filter fun p ↦ ¬(intersectionRank L p.1 p.2 : ℝ) ≤ θ * L) =
      densePairs N H L J θ := by
    ext p
    simp only [mem_filter, not_le, densePairs]
  rw [hhigh] at hsplit
  change (∑ p ∈ low, w p) + denseCovariance N H L J θ = residualCovariance N H L J at hsplit
  linarith only [hsplit, hlow]

end PaperP1.PrincipalResidualDensity
