module

public import PaperP1.Model.AllPairDependencyGraph

/-! # The literal positive residual and local mass in companion T19.14 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairResidualMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

def badEdges (H : ℝ) (N L : ℕ) : Finset (Finset ℕ) :=
  AllPairDependencyGraph.edges (RegularStarts.regularStarts N L) L \ GoodEdgeCompression.goodEdges H N L

def badMass (H : ℝ) (N L : ℕ) : ℝ := ∑ e ∈ badEdges H N L, infiniteJointMoment L e

def localMass (N L : ℕ) : ℝ := ∑ x ∈ RegularStarts.irregularStarts N L, infiniteMarginal x L

def tau (H : ℝ) (N L : ℕ) : ℝ := badMass H N L + localMass N L

theorem badMass_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ badMass H N L :=
  sum_nonneg (fun e _he ↦ infiniteJointMoment_nonneg L e)

theorem localMass_nonneg (N L : ℕ) : 0 ≤ localMass N L :=
  sum_nonneg (fun x _hx ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)

theorem tau_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ tau H N L :=
  add_nonneg (badMass_nonneg H N L) (localMass_nonneg N L)

theorem finite_bound (H : ℝ) (N L : ℕ) (hL : 0 < L) :
    tau H N L ≤
      (∑ e ∈ ClosePairs.pairs (RegularStarts.regularStarts N L) L, infiniteJointMoment L e) +
        RetainedBoundaryPositiveMass.badActivity H N L / 2 + localMass N L := by
  have hh := AllPairDependencyGraph.bad_mass_bound H N L hL (RegularStarts.regularStarts N L)
  change badMass H N L ≤ _ at hh
  unfold tau RetainedBoundaryPositiveMass.badActivity
  linarith only [hh]

end PaperP1.AllPairResidualMass
