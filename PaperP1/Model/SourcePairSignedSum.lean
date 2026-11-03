module

public import PaperP1.Model.SourcePairAffineWeight
public import PaperP1.Combinatorics.OrderedPairTuples
public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Model.RegularCumulantTransfer
public import PaperP1.Model.MissingBlockProbabilities

/-! # Exact nominally scaled ordered arithmetic pair sums and the actual factorial cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairSignedSum

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.FactorialCountMoments PaperP1.SourcePairAffineWeight

theorem ordered_joint_sum {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    (∑ p ∈ OrderedPairTuples.pairs G, infiniteJointMoment L {p.1, p.2}) = factorialCountMoment G L 2 := by
  rw [OrderedPairTuples.weighted_subsets G (infiniteJointMoment L), factorialCountMoment_eq_subset hG]
  norm_num

theorem ordered_card (G : Finset ℕ) :
    ((OrderedPairTuples.pairs G).card : ℝ) = (G.card : ℝ) ^ 2 - G.card := by
  have heq : OrderedPairTuples.pairs G = G.offDiag := by
    ext p
    simp only [OrderedPairTuples.pairs, mem_filter, mem_product, mem_offDiag]
    tauto
  rw [heq, offDiag_card, Nat.cast_sub (Nat.le_mul_self G.card), Nat.cast_mul]
  ring

theorem scaled_sum {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (hL : 0 < L) :
    ((2 ^ L : ℝ)⁻¹) ^ 2 * (∑ p ∈ OrderedPairTuples.pairs G, signedWeight p.1 p.2 L) =
      RegularCumulantTransfer.secondFactorialCumulant G L + countMoment G L 1 ^ 2 -
        ((G.card : ℝ) * (2 ^ L : ℝ)⁻¹) ^ 2 + (G.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  calc
    _ = ∑ p ∈ OrderedPairTuples.pairs G, ((2 ^ L : ℝ)⁻¹) ^ 2 * signedWeight p.1 p.2 L := mul_sum _ _ _
    _ = ∑ p ∈ OrderedPairTuples.pairs G,
        (infiniteJointMoment L {p.1, p.2} - ((2 ^ L : ℝ)⁻¹) ^ 2) :=
      sum_congr rfl (fun p _ ↦ scaled_signed_weight p.1 p.2 L hL)
    _ = factorialCountMoment G L 2 - ((OrderedPairTuples.pairs G).card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
      rw [sum_sub_distrib, ordered_joint_sum hG, sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [factorialCountMoment_two hG, ordered_card]
      unfold RegularCumulantTransfer.secondFactorialCumulant
      ring

theorem centering_error {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (hL : 0 < L) :
    |((2 ^ L : ℝ)⁻¹) ^ 2 * (∑ p ∈ OrderedPairTuples.pairs G, signedWeight p.1 p.2 L) -
      RegularCumulantTransfer.secondFactorialCumulant G L| ≤
      (countMoment G L 1 + (G.card : ℝ) * (2 ^ L : ℝ)⁻¹) *
        |countMoment G L 1 - (G.card : ℝ) * (2 ^ L : ℝ)⁻¹| +
          (G.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  have hmu : 0 ≤ countMoment G L 1 := by
    rw [countMoment_one hG]
    exact sum_nonneg (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hlam : 0 ≤ (G.card : ℝ) * (2 ^ L : ℝ)⁻¹ := by positivity
  rw [scaled_sum hG hL]
  have heq : RegularCumulantTransfer.secondFactorialCumulant G L + countMoment G L 1 ^ 2 -
      ((G.card : ℝ) * (2 ^ L : ℝ)⁻¹) ^ 2 + (G.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 -
      RegularCumulantTransfer.secondFactorialCumulant G L =
      (countMoment G L 1 + (G.card : ℝ) * (2 ^ L : ℝ)⁻¹) *
        (countMoment G L 1 - (G.card : ℝ) * (2 ^ L : ℝ)⁻¹) +
          (G.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by ring
  rw [heq]
  exact (abs_add_le _ _).trans_eq (by
    rw [abs_mul, abs_of_nonneg (add_nonneg hmu hlam), abs_of_nonneg (by positivity :
      0 ≤ (G.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2)])

end PaperP1.SourcePairSignedSum
