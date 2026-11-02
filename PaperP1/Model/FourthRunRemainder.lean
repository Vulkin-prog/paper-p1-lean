module

public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Model.HeterogeneousDirectMaximum
public import PaperP1.Algebra.FourthRepeatedIndexCost
public import PaperP1.Model.CompatibleActivitySplit

/-! # The exact actual fourth-cumulant remainder after unrestricted activities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthRunRemainder

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FourthRunFactorialCumulant
  PaperP1.HeterogeneousDirectMaximum

def remainder (G : Finset ℕ) (L : ℕ) : ℝ :=
  fourthFactorialCumulant G L - 24 * CompatibleActivitySplit.signed L (G.powersetCard 4) +
    12 * CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2

theorem exact_cost {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    remainder G L = FourthRepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G := by
  rw [remainder, FourthRunFactorialCumulant.exact_formula hG]
  unfold FourthRepeatedIndexCost.cost FourthRepeatedIndexCost.tripleTerm FourthRepeatedIndexCost.pairTerm
    CompatibleActivitySplit.signed
  ring

theorem finite_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (P : ℝ) (hP : 0 ≤ P)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P) :
    |remainder G L| ≤ 72 * P * CompatibleActivitySplit.absolute L (G.powersetCard 3) +
      72 * P ^ 2 * CompatibleActivitySplit.absolute L (G.powersetCard 2) + 6 * P ^ 3 * actualMean G L := by
  rw [exact_cost hG]
  exact FourthRepeatedIndexCost.bound _ _ G P hP
    (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) hcap

end PaperP1.FourthRunRemainder
