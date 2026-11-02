module

public import PaperP1.Algebra.ThirdFactorialCumulant
public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Model.InfiniteTripleCancellation

/-! # The actual original run count has the complete third factorial cumulant identity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThirdRunFactorialCumulant

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables

def thirdFactorialCumulant (G : Finset ℕ) (L : ℕ) : ℝ :=
  factorialCountMoment G L 3 - 3 * factorialCountMoment G L 2 * factorialCountMoment G L 1 +
    2 * (factorialCountMoment G L 1) ^ 3

theorem eq_subset_data {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    thirdFactorialCumulant G L = ThirdFactorialCumulant.fromSubsetData
      (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) G := by
  have hf2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  have hf3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
  rw [thirdFactorialCumulant, factorialCountMoment_eq_subset hG 3,
    factorialCountMoment_eq_subset hG 2, factorialCountMoment_one, countMoment_one hG, hf2, hf3]
  unfold ThirdFactorialCumulant.fromSubsetData ThirdFactorialCumulant.jointSum
  ring

theorem exact_formula {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    thirdFactorialCumulant G L =
      6 * (∑ T ∈ G.powersetCard 3, infiniteCenteredCoefficient L T) -
      6 * (∑ e ∈ G.powersetCard 2, (∑ x ∈ e, infiniteMarginal x L) * infiniteCenteredCoefficient L e) +
      2 * ∑ x ∈ G, (infiniteMarginal x L) ^ 3 := by
  rw [eq_subset_data hG]
  simpa only [← InfiniteTripleCancellation.coefficient_eq_transform] using
    ThirdFactorialCumulant.exact_formula (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) G
      (infiniteJointMoment_empty L) (InfiniteTripleCancellation.singleton_joint L)

end PaperP1.ThirdRunFactorialCumulant
