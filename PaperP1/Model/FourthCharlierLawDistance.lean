module

public import PaperP1.Model.OriginalLawPolynomialMoments
public import PaperP1.Probability.FourthCharlierReference
public import PaperP1.Probability.PoissonPolynomialMoments
public import PaperP1.Probability.SignedAtomicDistance
public import PaperP1.Analysis.PolynomialTestTruncation

/-! # The exact original-law fourth Charlier obstruction controls the full signed distance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthCharlierLawDistance

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum PaperP1.AtomicProbability
  PaperP1.PoissonSequence

theorem distance_eq_sequence (P : ProbabilityMeasure ℕ) (μ α : ℝ) (hμ : 0 ≤ μ) :
    SignedAtomicDistance.distance (P : Measure ℕ).toSignedMeasure (QuadraticPoisson.reference μ α) =
      ∑' k : ℕ, |realMass P k - quadraticMass μ α k| := by
  unfold SignedAtomicDistance.distance
  apply tsum_congr
  intro k
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k),
    QuadraticPoisson.reference, AtomicSignedLaw.ofSequence_singleton (hasSum_quadraticMass μ α hμ).summable]
  rfl

theorem finite_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    (r : ℕ) (hr : 4 ≤ r) (M R B : ℝ) (hmean : actualMean G L ≤ M) (hR : 1 ≤ R)
    (hq : Summable (fun k : ℕ ↦
      |quadraticMass (actualMean G L) (RegularCumulantTransfer.secondFactorialCumulant G L) k| *
        (1 + (k : ℝ)) ^ r))
    (hB : (∑' k : ℕ,
      |quadraticMass (actualMean G L) (RegularCumulantTransfer.secondFactorialCumulant G L) k| *
        (1 + (k : ℝ)) ^ r) ≤ B) :
    |FourthRunFactorialCumulant.fourthFactorialCumulant G L +
        3 * RegularCumulantTransfer.secondFactorialCumulant G L ^ 2| ≤
      (1 + M) ^ 4 * R ^ 4 *
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (actualMean G L) (RegularCumulantTransfer.secondFactorialCumulant G L)) +
      ((1 + M) ^ 4 / R ^ (r - 4)) * ((2 : ℝ) ^ r * (1 + countMoment G L r) + B) := by
  let μ := actualMean G L
  let α := RegularCumulantTransfer.secondFactorialCumulant G L
  let P := RetainedModifiedLaw.originalLaw G L
  let a := fun k : ℕ ↦ realMass P k - quadraticMass μ α k
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have ha : Summable a := (hasSum_realMass P).summable.sub (hasSum_quadraticMass μ α hμ).summable
  obtain ⟨hp, hpB⟩ := OriginalLawPolynomialMoments.weighted_moment_bound G L r
  have hweight (k : ℕ) : |a k| * (1 + (k : ℝ)) ^ r ≤
      realMass P k * (1 + (k : ℝ)) ^ r + |quadraticMass μ α k| * (1 + (k : ℝ)) ^ r := by
    have h := abs_sub (realMass P k) (quadraticMass μ α k)
    rw [abs_of_nonneg (realMass_nonneg P k)] at h
    have ht := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (1 + (k : ℝ)) ^ r)
    dsimp only [a]
    linarith only [ht]
  have hmoment := Summable.of_nonneg_of_le (fun k ↦ by positivity) hweight (hp.add hq)
  have hmomentB : (∑' k : ℕ, |a k| * (1 + (k : ℝ)) ^ r) ≤
      (2 : ℝ) ^ r * (1 + countMoment G L r) + B := by
    have h := hmoment.tsum_le_tsum hweight (hp.add hq)
    rw [hp.tsum_add hq] at h
    exact h.trans (add_le_add hpB hB)
  have he := (OriginalLawPolynomialMoments.charlier_hasSum (L := L) hG).sub
    (FourthCharlierReference.hasSum_zero μ α hμ)
  have htest : HasSum (fun k : ℕ ↦ a k * FourthCharlierPolynomial.value μ k)
      (FourthRunFactorialCumulant.fourthFactorialCumulant G L + 3 * α ^ 2) := by
    convert he using 1
    · funext k; dsimp only [a, P, μ, α]; ring
    · simp only [sub_zero, α]
  have hb := (PolynomialTestTruncation.test_bound a (FourthCharlierPolynomial.value μ) 4 r hr
    ((1 + M) ^ 4) R (by positivity) hR ha hmoment
    (fun k ↦ FourthCharlierPolynomial.envelope hμ hmean k)).2
  rw [htest.tsum_eq] at hb
  have hdist := distance_eq_sequence P μ α hμ
  rw [← hdist] at hb
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmomentB (by positivity)))

end PaperP1.FourthCharlierLawDistance
