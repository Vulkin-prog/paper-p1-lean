module

public import PaperP1.Model.HeterogeneousDirectMaximum
public import PaperP1.Model.CompatibleActivitySplit
public import PaperP1.Combinatorics.UnorderedPairRows

/-! # Actual pair rows and finite repeated-edge/shared-vertex product costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairRowActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Probability PaperP1.HeterogeneousDirectMaximum

def jointRow (G : Finset ℕ) (L x : ℕ) : ℝ := ∑ y ∈ G, infiniteJointMoment L {x, y}

def absoluteRow (G : Finset ℕ) (L x : ℕ) : ℝ :=
  ∑ y ∈ G.erase x, |infiniteCenteredCoefficient L {x, y}|

def repeatedSquare (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e ^ 2

def starSquare (G : Finset ℕ) (L : ℕ) : ℝ := ∑ x ∈ G, absoluteRow G L x ^ 2

theorem marginal_le_one (x L : ℕ) : infiniteMarginal x L ≤ 1 := by
  rw [infiniteMarginal_eq_finite (show x + L ≤ x + L from le_rfl)]
  exact exactMarginal_le_one _ _ x

theorem pair_absolute_bound (L x y : ℕ) (hxy : x ≠ y) :
    |infiniteCenteredCoefficient L {x, y}| ≤
      infiniteJointMoment L {x, y} + infiniteMarginal x L * infiniteMarginal y L := by
  rw [CompressedJointMoments.centered_pair L {x, y} (by simp [hxy]), prod_pair hxy]
  have hq := infiniteJointMoment_nonneg L {x, y}
  have hp := mul_nonneg (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (MissingBlockProbabilities.infiniteMarginal_nonneg y L)
  exact abs_le.mpr ⟨by linarith only [hq, hp], by linarith only [hq, hp]⟩

theorem pair_absolute_le_marginal (L x y : ℕ) (hxy : x ≠ y) :
    |infiniteCenteredCoefficient L {x, y}| ≤ infiniteMarginal x L := by
  rw [CompressedJointMoments.centered_pair L {x, y} (by simp [hxy]), prod_pair hxy]
  have hq := infiniteJointMoment_nonneg L {x, y}
  have hpx := MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hpy := MissingBlockProbabilities.infiniteMarginal_nonneg y L
  have hp := mul_nonneg hpx hpy
  have hprod : infiniteMarginal x L * infiniteMarginal y L ≤ infiniteMarginal x L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (marginal_le_one y L) hpx
  have hqpx : infiniteJointMoment L {x, y} ≤ infiniteMarginal x L := by
    simpa only [InfiniteTripleCancellation.singleton_joint] using
      MissingBlockProbabilities.infiniteJointMoment_antitone L (singleton_subset_iff.mpr (mem_insert_self x {y}))
  exact abs_le.mpr ⟨by linarith only [hq, hprod], by linarith only [hqpx, hp]⟩

theorem row_bound (G : Finset ℕ) (L x : ℕ) :
    absoluteRow G L x ≤ jointRow G L x + infiniteMarginal x L * actualMean G L := by
  calc
    _ ≤ ∑ y ∈ G.erase x, (infiniteJointMoment L {x, y} + infiniteMarginal x L * infiniteMarginal y L) := by
      apply sum_le_sum
      intro y hy
      exact pair_absolute_bound L x y (mem_erase.mp hy).1.symm
    _ = (∑ y ∈ G.erase x, infiniteJointMoment L {x, y}) +
        infiniteMarginal x L * ∑ y ∈ G.erase x, infiniteMarginal y L := by rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add
      (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun y _ _ ↦ infiniteJointMoment_nonneg L {x, y}))
      (mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          (fun y _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg y L))
        (MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem row_sum (G : Finset ℕ) (L : ℕ) :
    (∑ x ∈ G, absoluteRow G L x) = 2 * CompatibleActivitySplit.absolute L (G.powersetCard 2) :=
  UnorderedPairRows.sum_rows G (fun e ↦ |infiniteCenteredCoefficient L e|)

theorem repeated_square_bound (G : Finset ℕ) (L : ℕ) (P : ℝ)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P) :
    repeatedSquare G L ≤ P * CompatibleActivitySplit.absolute L (G.powersetCard 2) := by
  rw [CompatibleActivitySplit.absolute, mul_sum]
  apply sum_le_sum
  intro e he
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp he
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hecard
  have hp := (pair_absolute_le_marginal L x y hxy).trans (hcap x (heG (mem_insert_self _ _)))
  have h := mul_le_mul_of_nonneg_right hp (abs_nonneg (infiniteCenteredCoefficient L {x, y}))
  simpa only [← pow_two, sq_abs] using h

theorem star_square_bound (G : Finset ℕ) (L : ℕ) (P B : ℝ) (hB : 0 ≤ B)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P)
    (hrow : ∀ x ∈ G, absoluteRow G L x ≤ B * infiniteMarginal x L) :
    starSquare G L ≤ 2 * B * P * CompatibleActivitySplit.absolute L (G.powersetCard 2) := by
  calc
    _ ≤ ∑ x ∈ G, (B * P) * absoluteRow G L x := by
      apply sum_le_sum
      intro x hx
      have hn : 0 ≤ absoluteRow G L x := sum_nonneg fun y _ ↦ abs_nonneg (infiniteCenteredCoefficient L {x, y})
      have hb := mul_le_mul_of_nonneg_left (hcap x hx) hB
      have h := mul_le_mul_of_nonneg_right ((hrow x hx).trans hb) hn
      simpa only [pow_two] using h
    _ = (B * P) * ∑ x ∈ G, absoluteRow G L x := (mul_sum _ _ _).symm
    _ = _ := by rw [row_sum]; ring

end PaperP1.PairRowActivity
