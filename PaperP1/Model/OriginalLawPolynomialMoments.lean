module

public import PaperP1.Model.RetainedMomentTransfer
public import PaperP1.Model.RetainedModifiedLaw
public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Model.RegularCumulantTransfer
public import PaperP1.Algebra.FourthCharlierPolynomial

/-! # Actual original-law singleton sums for all polynomial tests and the fourth Charlier coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalLawPolynomialMoments

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.CountObservables PaperP1.FactorialCountMoments
  PaperP1.HeterogeneousDirectMaximum PaperP1.AtomicProbability

theorem original_hasSum (G : Finset ℕ) (L : ℕ) (f : ℕ → ℝ) :
    HasSum (fun k : ℕ ↦ realMass (RetainedModifiedLaw.originalLaw G L) k * f k)
      (∫ ω, f (infiniteStartCount G L ω) ∂infiniteRademacherMeasure) := by
  have hi : Integrable f (RetainedModifiedLaw.originalLaw G L : Measure ℕ) :=
    FiniteObservationLaw.integrable _ _ f
  have hsum := (AtomicTests.integrable_iff_summable _ f).mp hi
  have hs : Summable (fun k : ℕ ↦ realMass (RetainedModifiedLaw.originalLaw G L) k * f k) := by
    apply hsum.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (realMass_nonneg _ _)]
  have heq := AtomicTests.expectation_eq_integral _ f hi
  rw [RetainedModifiedLaw.originalLaw, FiniteObservationLaw.integral_eq,
    ← RetainedMomentTransfer.original_observable_integral] at heq
  exact heq ▸ hs.hasSum

theorem ordinary_hasSum (G : Finset ℕ) (L r : ℕ) :
    HasSum (fun k : ℕ ↦ realMass (RetainedModifiedLaw.originalLaw G L) k * (k : ℝ) ^ r)
      (countMoment G L r) := original_hasSum G L _

theorem factorial_hasSum (G : Finset ℕ) (L r : ℕ) :
    HasSum (fun k : ℕ ↦ realMass (RetainedModifiedLaw.originalLaw G L) k * (k.descFactorial r : ℝ))
      (factorialCountMoment G L r) := original_hasSum G L _

theorem charlier_hasSum {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    HasSum (fun k : ℕ ↦ realMass (RetainedModifiedLaw.originalLaw G L) k *
      FourthCharlierPolynomial.value (actualMean G L) k)
      (FourthRunFactorialCumulant.fourthFactorialCumulant G L +
        3 * RegularCumulantTransfer.secondFactorialCumulant G L ^ 2) := by
  let μ := actualMean G L
  have h4 := factorial_hasSum G L 4
  have h3 := factorial_hasSum G L 3
  have h2 := factorial_hasSum G L 2
  have h1 := ordinary_hasSum G L 1
  simp only [pow_one] at h1
  have h0 := hasSum_realMass (RetainedModifiedLaw.originalLaw G L)
  have h := (((h4.sub (h3.mul_left (4 * μ))).add (h2.mul_left (6 * μ ^ 2))).sub
    (h1.mul_left (4 * μ ^ 3))).add (h0.mul_left (μ ^ 4))
  convert h using 1
  · funext k; dsimp only [FourthCharlierPolynomial.value, μ]; ring
  · rw [FourthRunFactorialCumulant.fourthFactorialCumulant, RegularCumulantTransfer.secondFactorialCumulant,
      factorialCountMoment_one, factorialCountMoment_two hG, countMoment_one hG]
    dsimp only [μ, actualMean]
    ring

theorem weighted_moment_bound (G : Finset ℕ) (L r : ℕ) :
    Summable (fun k : ℕ ↦ realMass (RetainedModifiedLaw.originalLaw G L) k * (1 + (k : ℝ)) ^ r) ∧
      (∑' k : ℕ, realMass (RetainedModifiedLaw.originalLaw G L) k * (1 + (k : ℝ)) ^ r) ≤
        (2 : ℝ) ^ r * (1 + countMoment G L r) := by
  have hs := (original_hasSum G L (fun k ↦ (1 + (k : ℝ)) ^ r)).summable
  have hm := ordinary_hasSum G L r
  have h0 := hasSum_realMass (RetainedModifiedLaw.originalLaw G L)
  have hpoint (k : ℕ) : (1 + (k : ℝ)) ^ r ≤ (2 : ℝ) ^ r * (1 + (k : ℝ) ^ r) := by
    have h := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg k) r
    rw [one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : r - 1 ≤ r)) (by positivity))
  have hb := hs.tsum_le_tsum
    (fun k ↦ mul_le_mul_of_nonneg_left (hpoint k) (realMass_nonneg _ _))
    (((h0.summable.add hm.summable).mul_left ((2 : ℝ) ^ r)).congr (fun k ↦ by ring))
  have heq : (∑' k : ℕ, realMass (RetainedModifiedLaw.originalLaw G L) k *
      ((2 : ℝ) ^ r * (1 + (k : ℝ) ^ r))) = (2 : ℝ) ^ r * (1 + countMoment G L r) := by
    have ht := (h0.add hm).mul_left ((2 : ℝ) ^ r)
    convert ht.tsum_eq using 1
    congr 1
    funext k
    ring
  exact ⟨hs, hb.trans_eq heq⟩

end PaperP1.OriginalLawPolynomialMoments
