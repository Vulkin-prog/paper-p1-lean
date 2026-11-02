module

public import PaperP1.Algebra.FourthFactorialCumulant
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.PositiveJointRestriction

/-! # The actual fourth factorial cumulant and its complete heterogeneous identity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthRunFactorialCumulant

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables

def fourthFactorialCumulant (G : Finset ℕ) (L : ℕ) : ℝ :=
  factorialCountMoment G L 4 - 4 * factorialCountMoment G L 3 * factorialCountMoment G L 1 -
    3 * factorialCountMoment G L 2 ^ 2 + 12 * factorialCountMoment G L 2 * factorialCountMoment G L 1 ^ 2 -
    6 * factorialCountMoment G L 1 ^ 4

theorem eq_subset_data {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    fourthFactorialCumulant G L = FourthFactorialCumulant.fromSubsetData
      (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) G := by
  have hf2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  have hf3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
  have hf4 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num
  rw [fourthFactorialCumulant, factorialCountMoment_eq_subset hG 4,
    factorialCountMoment_eq_subset hG 3, factorialCountMoment_eq_subset hG 2,
    factorialCountMoment_one, countMoment_one hG, hf2, hf3, hf4]
  unfold FourthFactorialCumulant.fromSubsetData FourthFactorialCumulant.total
  ring

theorem exact_formula {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    fourthFactorialCumulant G L =
      24 * (∑ I ∈ G.powersetCard 4, infiniteCenteredCoefficient L I) -
      12 * (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) ^ 2 -
      24 * (∑ T ∈ G.powersetCard 3, infiniteCenteredCoefficient L T * ∑ x ∈ T, infiniteMarginal x L) +
      24 * (∑ e ∈ G.powersetCard 2,
        ((∑ x ∈ e, infiniteMarginal x L ^ 2) + ∏ x ∈ e, infiniteMarginal x L) * infiniteCenteredCoefficient L e) -
      6 * ∑ x ∈ G, infiniteMarginal x L ^ 4 := by
  rw [eq_subset_data hG]
  have h0 : infiniteCenteredCoefficient L ∅ = 1 := by
    rw [InfiniteTripleCancellation.coefficient_eq_transform, Algebra.centeredCoefficient_empty, infiniteJointMoment_empty]
  have h1 (x : ℕ) : infiniteCenteredCoefficient L {x} = 0 := by
    rw [InfiniteTripleCancellation.coefficient_eq_transform]
    exact Algebra.centeredCoefficient_singleton_eq_zero _ _ x (infiniteJointMoment_empty L)
      (InfiniteTripleCancellation.singleton_joint L x)
  have h := FourthFactorialCumulant.exact_formula G (fun x ↦ infiniteMarginal x L)
    (infiniteJointMoment L) (infiniteCenteredCoefficient L)
    (fun I _ ↦ CompressedJointMoments.infinite_uncentered_expansion L I) h0 h1
  simpa only [FourthFactorialCumulant.total, FourthFactorialCumulant.weighted,
    FourthFactorialCumulant.pairSquare_eq] using h

theorem zero_marginal_restriction {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    fourthFactorialCumulant G L = fourthFactorialCumulant (PositiveMarginalRestriction.positiveGround G L) L := by
  simp only [fourthFactorialCumulant, PositiveJointRestriction.factorial_restrict hG]

end PaperP1.FourthRunFactorialCumulant
