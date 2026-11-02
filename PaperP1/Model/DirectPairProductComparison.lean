module

public import PaperP1.Model.PairRowActivity
public import PaperP1.Algebra.PairProductComparison
public import PaperP1.Combinatorics.SharedPairProducts

/-! # Actual direct pair products and the remaining disjoint non-direct cost

All populations and weights are literal finite original-model data. The
non-direct cost is retained in the conclusion, not assumed to satisfy a
target asymptotic estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectPairProductComparison

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

def Direct (L : ℕ) (S : Finset (Finset ℕ)) : Prop :=
  runRelativeNullity L (S.biUnion id) = ∑ e ∈ S, runRelativeNullity L e

def directPairs (G : Finset ℕ) (L : ℕ) : Finset (Finset (Finset ℕ)) := by
  classical
  exact ((G.powersetCard 2).powersetCard 2).filter
    (fun S ↦ S ∉ SharedPairProducts.overlapping G ∧ Direct L S)

def nonDirectApartPairs (G : Finset ℕ) (L : ℕ) : Finset (Finset (Finset ℕ)) := by
  classical
  exact ((G.powersetCard 2).powersetCard 2).filter
    (fun S ↦ S ∉ SharedPairProducts.overlapping G ∧ ¬Direct L S)

def signedDirect (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ S ∈ directPairs G L, ∏ e ∈ S, infiniteCenteredCoefficient L e

def nonDirectApartCost (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ S ∈ nonDirectApartPairs G L, ∏ e ∈ S, |infiniteCenteredCoefficient L e|

theorem direct_pair_iff (L : ℕ) (e f : Finset ℕ) (hef : e ≠ f) :
    Direct L {e, f} ↔
      runRelativeNullity L (e ∪ f) = runRelativeNullity L e + runRelativeNullity L f := by
  simp only [Direct, biUnion_insert, singleton_biUnion, id_eq, sum_pair hef]

theorem nonDirectApartCost_nonneg (G : Finset ℕ) (L : ℕ) :
    0 ≤ nonDirectApartCost G L :=
  sum_nonneg fun _S _ ↦ prod_nonneg fun _e _ ↦ abs_nonneg _

theorem omitted_decomposition (G : Finset ℕ) (L : ℕ) :
    (G.powersetCard 2).powersetCard 2 \ directPairs G L =
      SharedPairProducts.overlapping G ∪ nonDirectApartPairs G L := by
  classical
  ext S
  have hsub := SharedPairProducts.overlapping_subset G
  by_cases hS : S ∈ (G.powersetCard 2).powersetCard 2
  · by_cases ho : S ∈ SharedPairProducts.overlapping G <;>
      by_cases hd : Direct L S <;>
      simp [directPairs, nonDirectApartPairs, hS, ho, hd]
  · have ho : S ∉ SharedPairProducts.overlapping G := fun h ↦ hS (hsub h)
    simp [directPairs, nonDirectApartPairs, hS, ho]

theorem overlapping_disjoint_nonDirect (G : Finset ℕ) (L : ℕ) :
    Disjoint (SharedPairProducts.overlapping G) (nonDirectApartPairs G L) := by
  classical
  apply disjoint_left.mpr
  intro S ho hb
  exact (mem_filter.mp hb).2.1 ho

theorem finite_bound (G : Finset ℕ) (L : ℕ) :
    |CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2 / 2 - signedDirect G L| ≤
      (PairRowActivity.repeatedSquare G L + PairRowActivity.starSquare G L) / 2 +
        nonDirectApartCost G L := by
  classical
  have hsplit := PairProductComparison.absolute_bound (infiniteCenteredCoefficient L)
    (G.powersetCard 2) (directPairs G L) (filter_subset _ _)
  change |CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2 / 2 - signedDirect G L| ≤
    PairRowActivity.repeatedSquare G L / 2 +
      ∑ S ∈ (G.powersetCard 2).powersetCard 2 \ directPairs G L,
        ∏ e ∈ S, |infiniteCenteredCoefficient L e| at hsplit
  rw [omitted_decomposition, sum_union (overlapping_disjoint_nonDirect G L)] at hsplit
  have hshared := SharedPairProducts.overlapping_bound G
    (fun e ↦ |infiniteCenteredCoefficient L e|) (fun e ↦ abs_nonneg _)
  change (∑ S ∈ SharedPairProducts.overlapping G, ∏ e ∈ S, |infiniteCenteredCoefficient L e|) ≤
    PairRowActivity.starSquare G L / 2 at hshared
  unfold nonDirectApartCost
  linarith only [hsplit, hshared]

end PaperP1.DirectPairProductComparison
