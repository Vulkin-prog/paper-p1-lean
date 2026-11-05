module

public import PaperP1.Model.DependentPairUnionSeeds
public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Asymptotics.NoSingletonJointMass

/-! # A coarse positive two-edge bound for every actual dependent-pair family

This rate one estimate suffices for intensity restoration. The sharper
O(a_N^2) good-edge estimate is a separate, still open assertion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairSecondMoment

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher

theorem uniform_joint_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ E : Finset (Finset ℕ),
      (∀ e ∈ E, e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e) →
      (∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := NoSingletonJointMass.uniform_weighted 4 4 C ε (by norm_num) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG E hE
  exact (DependentPairUnionSeeds.joint_bound L E).trans
    (h N hN L hband G hG (DependentPairUnionSeeds.families E)
      (DependentPairUnionSeeds.family_data G L E hE))

theorem uniform_factorial_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ E : Finset (Finset ℕ),
      (∀ e ∈ E, e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e) →
      (∫ ω, (ActiveEdgeObservables.value E L ω ^ 2 - ActiveEdgeObservables.value E L ω)
        ∂infiniteRademacherMeasure) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_joint_bound C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG E hE
  have hcut : ∀ e ∈ E, ∀ x ∈ e, x + L ≤ 2 * N + L := by
    intro e he x hx
    have hh := (mem_Ico.mp (hG ((hE e he).1 hx))).2
    omega
  rw [ActiveFamilySecondMoment.infinite_mean_eq E hcut]
  exact h N hN L hband G hG E hE

theorem uniform_good_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      (∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_joint_bound C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H
  exact h N hN L hband (dyadicBlock N) Subset.rfl (GoodEdgeCompression.goodEdges H N L)
    (fun e he ↦ ⟨(RetainedGoodEdges.good_pair_regular (by omega) e he).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L e he,
      RetainedGoodEdges.good_pair_positive H N L e he⟩)

end PaperP1.DependentPairSecondMoment
