module

public import PaperP1.Model.ActiveEdgeObservables
public import PaperP1.Probability.PositiveCountBonferroni
public import PaperP1.Model.PrincipalChannelEdges

/-! # Exact actual good-edge factorial second moment and union correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveEdgeBonferroni

open Finset MeasureTheory PaperP1.Algebra PaperP1.Arithmetic PaperP1.Probability
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.ActiveEdgeObservables

def factorialSecond (F : Finset (Finset ℕ)) (L : ℕ) : ℝ :=
  ∫ ω, value F L ω * (value F L ω - 1) ∂infiniteRademacherMeasure

theorem factorialSecond_eq_finite {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    factorialSecond F L = finiteExpectation (cylinderProbability M).weight (fun σ ↦
      ActivePairCount.value F (fun x ↦ startIndicator x L) σ *
        (ActivePairCount.value F (fun x ↦ startIndicator x L) σ - 1)) :=
  integral_eq_finite F hcut (fun x ↦ x * (x - 1))

theorem union_correction {M L : ℕ} (F : Finset (Finset ℕ))
    (hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) :
    0 ≤ (∑ e ∈ F, infiniteJointMoment L e) - probability F L ∧
      (∑ e ∈ F, infiniteJointMoment L e) - probability F L ≤ factorialSecond F L / 2 := by
  rw [← finite_mean_eq F hcut, probability_eq_finite F hcut, factorialSecond_eq_finite F hcut]
  exact PositiveCountBonferroni.finite_bound (cylinderProbability M)
    (ActivePairCount.value F (fun x ↦ startIndicator x L)) (fun σ ↦
      ⟨_, ActivePairCount.value_eq_card F (fun x ↦ startIndicator x L) σ⟩)

theorem principal_mean_and_union {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    (∫ ω, value (PrincipalChannelEdges.edges N H L) L ω ∂infiniteRademacherMeasure) =
      PrincipalChannelEdges.beta N H L ∧
    0 ≤ PrincipalChannelEdges.beta N H L - probability (PrincipalChannelEdges.edges N H L) L ∧
      PrincipalChannelEdges.beta N H L - probability (PrincipalChannelEdges.edges N H L) L ≤
        factorialSecond (PrincipalChannelEdges.edges N H L) L / 2 := by
  have hF := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
  have hcut : ∀ e ∈ PrincipalChannelEdges.edges N H L, ∀ x ∈ e, x + L ≤ dyadicCutoff N L := fun e he x hx ↦
    CountObservables.dyadic_subset_cutoff (subset_refl (dyadicBlock N)) x ((mem_powersetCard.mp (hF he)).1 hx)
  exact ⟨mean_eq _ hcut, union_correction _ hcut⟩

end PaperP1.ActiveEdgeBonferroni
