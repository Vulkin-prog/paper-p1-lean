module

public import PaperP1.Model.ThirdRunFactorialCumulant
public import PaperP1.Algebra.RepeatedIndexCost
public import PaperP1.Model.TripleActivityConnected

/-! # Exact third-cumulant comparison with all repeated-index and incompatible costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThirdRunActivityComparison

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ThirdRunFactorialCumulant
  PaperP1.TripleActivityConnected

theorem exact_decomposition {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    thirdFactorialCumulant G L = 6 * CompatibleActivitySplit.signed L (G.powersetCard 3) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G := by
  rw [exact_formula hG]
  unfold CompatibleActivitySplit.signed RepeatedIndexCost.cost
  ring

theorem repeated_cost_bound (G : Finset ℕ) (L : ℕ) (P : ℝ) (hP : 0 ≤ P)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P) :
    |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      12 * P * CompatibleActivitySplit.absolute L (G.powersetCard 2) +
        2 * P ^ 2 * ∑ x ∈ G, infiniteMarginal x L :=
  RepeatedIndexCost.bound _ _ G P hP
    (fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L) hcap

theorem finite_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (hL : 0 < L)
    (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) (P : ℝ) (hP : 0 ≤ P)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P) :
    |thirdFactorialCumulant G L - 6 * positiveConnected L (G.powersetCard 3)| ≤
      6 * CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) +
      12 * P * CompatibleActivitySplit.absolute L (G.powersetCard 2) +
        2 * P ^ 2 * ∑ x ∈ G, infiniteMarginal x L := by
  have herror := signed_comparison L hL (G.powersetCard 3)
    (fun I hI ↦ (mem_powersetCard.mp hI).2)
    (fun I hI x hx ↦ hp x ((mem_powersetCard.mp hI).1 hx))
  have hrepeat := repeated_cost_bound G L P hP hcap
  rw [exact_decomposition hG]
  have hid : 6 * CompatibleActivitySplit.signed L (G.powersetCard 3) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G -
      6 * positiveConnected L (G.powersetCard 3) =
      6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)) +
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G := by ring
  rw [hid]
  calc
    _ ≤ |6 * (CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3))| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := abs_add_le _ _
    _ = 6 * |CompatibleActivitySplit.signed L (G.powersetCard 3) - positiveConnected L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := by
      rw [abs_mul]
      norm_num
    _ ≤ 6 * CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) +
        (12 * P * CompatibleActivitySplit.absolute L (G.powersetCard 2) +
          2 * P ^ 2 * ∑ x ∈ G, infiniteMarginal x L) :=
      add_le_add (mul_le_mul_of_nonneg_left herror (by norm_num)) hrepeat
    _ = _ := by ring

end PaperP1.ThirdRunActivityComparison
