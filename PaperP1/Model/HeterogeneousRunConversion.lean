module

public import PaperP1.Probability.HeterogeneousPoissonCharlierConversion
public import PaperP1.Model.ThirdRunFactorialCumulant
public import PaperP1.Model.RegularCumulantTransfer

/-! # Heterogeneous conversion with actual original-run marginals and covariance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousRunConversion

open Finset PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CountObservables PaperP1.FactorialCountMoments
  PaperP1.HeterogeneousBernoulli PaperP1.HeterogeneousPoissonCharlierConversion

theorem marginal_bounds (x L : ℕ) : 0 ≤ infiniteMarginal x L ∧ infiniteMarginal x L ≤ 1 := by
  rw [infiniteMarginal_eq_finite (le_refl (x + L))]
  exact ⟨exactMarginal_nonneg _ _ _, exactMarginal_le_one _ _ _⟩

theorem covariance_sum_eq (G : Finset ℕ) (L : ℕ) :
    covarianceSum (G.powersetCard 2) (infiniteCenteredCoefficient L) =
      (∑ e ∈ G.powersetCard 2, infiniteJointMoment L e) -
        SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G 2 := by
  rw [covarianceSum, SubsetPowerSums.elementary, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  rw [InfiniteTripleCancellation.coefficient_eq_transform]
  exact ThirdFactorialCumulant.pair_formula _ _ (infiniteJointMoment_empty L)
    (InfiniteTripleCancellation.singleton_joint L) e (mem_powersetCard.mp he).2

theorem second_cumulant_formula {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    RegularCumulantTransfer.secondFactorialCumulant G L =
      2 * covarianceSum (G.powersetCard 2) (infiniteCenteredCoefficient L) -
        powerSum G (fun x ↦ infiniteMarginal x L) 2 := by
  rw [covariance_sum_eq, powerSum, RegularCumulantTransfer.secondFactorialCumulant,
    ← factorialCountMoment_two hG, factorialCountMoment_eq_subset hG 2,
    countMoment_one hG, SubsetPowerSums.square]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  ring

def reference (G : Finset ℕ) (L : ℕ) : SignedLaw ℝ :=
  finiteReference G (G.powersetCard 2) (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L)

def absoluteMass (G : Finset ℕ) (L : ℕ) : ℝ :=
  absolutePairMass (G.powersetCard 2) (infiniteCenteredCoefficient L)

theorem absoluteMass_nonneg (G : Finset ℕ) (L : ℕ) : 0 ≤ absoluteMass G L :=
  sum_nonneg (fun _ _ ↦ abs_nonneg _)

/-- Every covariance has its actual sign, including incompatible pairs. No
independence, pair-probability cap, or arithmetic asymptotic estimate is used. -/
theorem actual_signed_measure_conversion {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    {P M : ℝ} (hP : 0 ≤ P) (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P)
    (hmean : countMoment G L 1 ≤ M) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
      QuadraticPoisson.reference (countMoment G L 1)
        (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
      constant M * (powerSum G (fun x ↦ infiniteMarginal x L) 3 +
        (powerSum G (fun x ↦ infiniteMarginal x L) 2) ^ 2 +
        absoluteMass G L * (powerSum G (fun x ↦ infiniteMarginal x L) 2 + P)) := by
  rw [second_cumulant_formula hG, countMoment_one hG]
  exact HeterogeneousPoissonCharlierConversion.actual_signed_measure_conversion
    G (G.powersetCard 2) (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L)
    (fun _e he ↦ mem_powersetCard.mp he) (fun x _ ↦ marginal_bounds x L) hP hcap
    (by simpa only [mean, ← countMoment_one hG] using hmean)

end PaperP1.HeterogeneousRunConversion
