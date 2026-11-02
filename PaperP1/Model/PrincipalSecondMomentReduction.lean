module

public import PaperP1.Model.AlignedPrincipalEdgePairs
public import PaperP1.Model.SharedPrincipalEdgePairs

/-! # The actual principal-edge second moment reduces to a literal residual covariance sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalSecondMomentReduction

open Finset PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges PaperP1.PrincipalEdgeSpaces

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def residualPairs (N H L J : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (factorialPairs N H L).filter fun p ↦ Disjoint p.1 p.2 ∧
    ¬AlignedPrincipalEdgePairs.HasSeed N L J (p.1 ∪ p.2) ∧ ¬Disjoint (space L p.1) (space L p.2)

def residualCovariance (N H L J : ℕ) : ℝ := ∑ p ∈ residualPairs N H L J,
  |infiniteJointMoment L (p.1 ∪ p.2) - infiniteJointMoment L p.1 * infiniteJointMoment L p.2|

theorem residual_nonneg (N H L J : ℕ) : 0 ≤ residualCovariance N H L J :=
  sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem finite_upper {N H L J : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 29 * (L + 1) < N) :
    jointSecond N H L ≤ beta N H L ^ 2 + SharedPrincipalEdgePairs.contribution N H L +
      AlignedPrincipalEdgePairs.contribution N H L J + residualCovariance N H L J := by
  let P := (edges N H L) ×ˢ (edges N H L)
  let q := fun p : Finset ℕ × Finset ℕ ↦ infiniteJointMoment L (p.1 ∪ p.2)
  let b := fun p : Finset ℕ × Finset ℕ ↦ infiniteJointMoment L p.1 * infiniteJointMoment L p.2
  have hSsub : SharedPrincipalEdgePairs.pairs N H L ⊆ P := fun _ hp ↦ (mem_filter.mp hp).1
  have hAsub : AlignedPrincipalEdgePairs.pairs N H L J ⊆ P := fun _ hp ↦
    (mem_filter.mp (mem_filter.mp hp).1).1
  have hRsub : residualPairs N H L J ⊆ P := fun _ hp ↦ (mem_filter.mp (mem_filter.mp hp).1).1
  have hfilter (R : Finset (Finset ℕ × Finset ℕ)) (hR : R ⊆ P) : P.filter (fun p ↦ p ∈ R) = R := by
    ext p
    exact ⟨fun hp ↦ (mem_filter.mp hp).2, fun hp ↦ mem_filter.mpr ⟨hR hp, hp⟩⟩
  have hpoint (p : Finset ℕ × Finset ℕ) (hp : p ∈ P) :
      (if p.1 ≠ p.2 then q p else 0) ≤ b p +
        (if p ∈ SharedPrincipalEdgePairs.pairs N H L then q p else 0) +
        (if p ∈ AlignedPrincipalEdgePairs.pairs N H L J then q p else 0) +
        (if p ∈ residualPairs N H L J then |q p - b p| else 0) := by
    have hb : 0 ≤ b p := mul_nonneg (infiniteJointMoment_nonneg L p.1) (infiniteJointMoment_nonneg L p.2)
    have hS : 0 ≤ if p ∈ SharedPrincipalEdgePairs.pairs N H L then q p else 0 := by
      split_ifs
      · exact infiniteJointMoment_nonneg L _
      · rfl
    have hA : 0 ≤ if p ∈ AlignedPrincipalEdgePairs.pairs N H L J then q p else 0 := by
      split_ifs
      · exact infiniteJointMoment_nonneg L _
      · rfl
    have hR : 0 ≤ if p ∈ residualPairs N H L J then |q p - b p| else 0 := by
      split_ifs
      · exact abs_nonneg _
      · rfl
    by_cases hne : p.1 ≠ p.2
    · rw [ite_eq_left hne]
      obtain ⟨he, hf⟩ := mem_product.mp hp
      by_cases hspaces : Disjoint (space L p.1) (space L p.2)
      · have heq : q p = b p := joint_factor hN hL hlarge he hf hspaces
        have hh := heq.le
        linarith only [hh, hS, hA, hR]
      · by_cases hset : Disjoint p.1 p.2
        · by_cases hseed : AlignedPrincipalEdgePairs.HasSeed N L J (p.1 ∪ p.2)
          · have hmem : p ∈ AlignedPrincipalEdgePairs.pairs N H L J :=
              mem_filter.mpr ⟨mem_filter.mpr ⟨hp, hne⟩, hset, hseed⟩
            rw [ite_eq_left hmem]
            linarith only [hb, hS, hR]
          · have hmem : p ∈ residualPairs N H L J :=
              mem_filter.mpr ⟨mem_filter.mpr ⟨hp, hne⟩, hset, hseed, hspaces⟩
            rw [ite_eq_left hmem]
            have hh := le_abs_self (q p - b p)
            linarith only [hh, hS, hA]
        · have hmem : p ∈ SharedPrincipalEdgePairs.pairs N H L := mem_filter.mpr ⟨hp, hne, hset⟩
          rw [ite_eq_left hmem]
          linarith only [hb, hA, hR]
    · rw [ite_eq_right hne]
      linarith only [hb, hS, hA, hR]
  have hbeta : (∑ p ∈ P, b p) = beta N H L ^ 2 := by
    rw [sum_product, ← sum_mul_sum, pow_two]
    rfl
  calc
    _ = ∑ p ∈ P, if p.1 ≠ p.2 then q p else 0 := by
      rw [jointSecond, factorialPairs, sum_filter]
    _ ≤ ∑ p ∈ P, (b p +
        (if p ∈ SharedPrincipalEdgePairs.pairs N H L then q p else 0) +
        (if p ∈ AlignedPrincipalEdgePairs.pairs N H L J then q p else 0) +
        (if p ∈ residualPairs N H L J then |q p - b p| else 0)) := sum_le_sum hpoint
    _ = _ := by
      simp only [sum_add_distrib, hbeta, ← sum_filter]
      rw [hfilter _ hSsub, hfilter _ hAsub, hfilter _ hRsub]
      rfl

theorem finite_residual_lower {N H L J : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 29 * (L + 1) < N) :
    residualCovariance N H L J ≤ jointSecond N H L - beta N H L ^ 2 + 2 * coupledProductMass N H L := by
  let P := (edges N H L) ×ˢ (edges N H L)
  let q := fun p : Finset ℕ × Finset ℕ ↦ infiniteJointMoment L (p.1 ∪ p.2)
  let b := fun p : Finset ℕ × Finset ℕ ↦ infiniteJointMoment L p.1 * infiniteJointMoment L p.2
  have hsub : residualPairs N H L J ⊆ P := fun _ hp ↦ (mem_filter.mp (mem_filter.mp hp).1).1
  have hfilter : P.filter (fun p ↦ p ∈ residualPairs N H L J) = residualPairs N H L J := by
    ext p
    exact ⟨fun hp ↦ (mem_filter.mp hp).2, fun hp ↦ mem_filter.mpr ⟨hsub hp, hp⟩⟩
  have hpoint (p : Finset ℕ × Finset ℕ) (hp : p ∈ P) :
      (if p ∈ residualPairs N H L J then |q p - b p| else 0) ≤
        ((if p.1 ≠ p.2 then q p else 0) - b p) +
          2 * (if ¬Disjoint (space L p.1) (space L p.2) then b p else 0) := by
    obtain ⟨he, hf⟩ := mem_product.mp hp
    have hb : 0 ≤ b p := mul_nonneg (infiniteJointMoment_nonneg L p.1) (infiniteJointMoment_nonneg L p.2)
    have hq : 0 ≤ q p := infiniteJointMoment_nonneg L _
    by_cases hspaces : Disjoint (space L p.1) (space L p.2)
    · have hnotres : p ∉ residualPairs N H L J := by
        intro hpR
        exact (mem_filter.mp hpR).2.2.2 hspaces
      have hne := independent_ne hN hL hlarge he hf hspaces
      have heq : q p = b p := joint_factor hN hL hlarge he hf hspaces
      rw [ite_eq_right hnotres, ite_eq_left hne, ite_eq_right (not_not.mpr hspaces)]
      linarith only [heq]
    · rw [ite_eq_left hspaces]
      by_cases hne : p.1 ≠ p.2
      · rw [ite_eq_left hne]
        by_cases hres : p ∈ residualPairs N H L J
        · rw [ite_eq_left hres]
          exact abs_le.mpr ⟨by linarith only [hq], by linarith only [hb]⟩
        · rw [ite_eq_right hres]
          linarith only [hb, hq]
      · have hnotres : p ∉ residualPairs N H L J := fun hpR ↦ hne (mem_filter.mp (mem_filter.mp hpR).1).2
        rw [ite_eq_right hne, ite_eq_right hnotres]
        linarith only [hb]
  have hbeta : (∑ p ∈ P, b p) = beta N H L ^ 2 := by
    rw [sum_product, ← sum_mul_sum, pow_two]
    rfl
  calc
    _ = ∑ p ∈ P, if p ∈ residualPairs N H L J then |q p - b p| else 0 := by
      rw [← sum_filter, hfilter]
      rfl
    _ ≤ ∑ p ∈ P, (((if p.1 ≠ p.2 then q p else 0) - b p) +
        2 * (if ¬Disjoint (space L p.1) (space L p.2) then b p else 0)) := sum_le_sum hpoint
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hbeta, ← sum_filter, ← sum_filter]
      rfl

end PaperP1.PrincipalSecondMomentReduction
