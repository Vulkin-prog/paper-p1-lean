module

public import PaperP1.Model.HeterogeneousRunConversion
public import PaperP1.Probability.UniversalHeterogeneousConversion

/-! # Actual run-reference conversion with a universal constant and no mean cap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniversalRunConversion

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.HeterogeneousBernoulli PaperP1.HeterogeneousRunConversion
  PaperP1.UniversalHeterogeneousConversion

theorem actual_signed_measure_conversion {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    {P : ℝ} (hP : 0 ≤ P) (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
      QuadraticPoisson.reference (countMoment G L 1)
        (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
      universalConstant * (powerSum G (fun x ↦ infiniteMarginal x L) 3 +
        (powerSum G (fun x ↦ infiniteMarginal x L) 2) ^ 2 +
        absoluteMass G L * (powerSum G (fun x ↦ infiniteMarginal x L) 2 + P)) := by
  rw [second_cumulant_formula hG, countMoment_one hG]
  exact UniversalHeterogeneousConversion.actual_signed_measure_conversion
    G (G.powersetCard 2) (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L)
    (fun _e he ↦ mem_powersetCard.mp he) (fun x _ ↦ marginal_bounds x L) hP hcap

end PaperP1.UniversalRunConversion
