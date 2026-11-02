module

public import PaperP1.Probability.CompoundPoissonExponential

/-! # Actual first and exponential moments of the compound references -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompoundPoissonMoments

open MeasureTheory PaperP1.PoissonSequence PaperP1.PoissonProduct PaperP1.CompoundPoissonSeries
  PaperP1.CompoundPoissonExponential

theorem hasSum_joint_mean (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasSum (fun z : ℕ × ℕ ↦ joint a b z * ((z.1 + j * z.2 : ℕ) : ℝ)) (a + (j : ℝ) * b) := by
  have hsL : Summable (fun z : ℕ × ℕ ↦ ((z.1 : ℝ) * mass a z.1) * mass b z.2) := by
    simpa only [joint, mul_assoc] using left_moment_summable ha hb
  have hL := (poisson_moment_hasSum ha).mul (hasSum_mass b hb) hsL
  have hsR : Summable (fun z : ℕ × ℕ ↦ mass a z.1 * ((z.2 : ℝ) * mass b z.2)) := by
    convert right_moment_summable ha hb using 1
    funext z
    unfold joint
    ring
  have hR := (hasSum_mass a ha).mul (poisson_moment_hasSum hb) hsR
  have h := hL.add (hR.mul_left (j : ℝ))
  simp only [mul_one, one_mul] at h
  convert h using 1
  funext z
  unfold joint
  push_cast
  ring

theorem hasSum_law_mean (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasSum (fun k : ℕ ↦ AtomicProbability.realMass (law j a b ha hb) k * (k : ℝ))
      (a + (j : ℝ) * b) := by
  have h := PushforwardMass.hasSum_map (hasSum_joint_mean j a b ha hb)
    (fun z : ℕ × ℕ ↦ z.1 + j * z.2)
  have heq (k : ℕ) : PushforwardMass.map (fun z : ℕ × ℕ ↦ z.1 + j * z.2)
      (fun z ↦ joint a b z * ((z.1 + j * z.2 : ℕ) : ℝ)) k =
        AtomicProbability.realMass (law j a b ha hb) k * (k : ℝ) := by
    simpa only [realMass_law] using PushforwardMass.map_mul
      (fun z : ℕ × ℕ ↦ z.1 + j * z.2) (joint a b) (fun k : ℕ ↦ (k : ℝ)) k
  convert h using 1
  funext k
  exact (heq k).symm

theorem integral_law_mean (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ k : ℕ, (k : ℝ) ∂(law j a b ha hb : Measure ℕ)) = a + (j : ℝ) * b := by
  have hs := hasSum_law_mean j a b ha hb
  have hi : Integrable (fun k : ℕ ↦ (k : ℝ)) (law j a b ha hb : Measure ℕ) := by
    apply (AtomicTests.integrable_iff_summable _ _).mpr
    have habs (k : ℕ) : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    simpa only [habs] using hs.summable
  rw [← AtomicTests.expectation_eq_integral _ _ hi]
  exact hs.tsum_eq

theorem integral_hermite_mean (μ α : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) :
    (∫ k : ℕ, (k : ℝ) ∂(HermiteReference.law μ α hα hαμ : Measure ℕ)) = μ := by
  have h := integral_law_mean 2 (μ - α) (α / 2) (sub_nonneg.mpr hαμ) (by positivity)
  simp only [Nat.cast_ofNat] at h
  rw [show μ - α + 2 * (α / 2) = μ by ring] at h
  exact h

theorem integral_law_exp (j : ℕ) (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ k : ℕ, Real.exp (t * k) ∂(law j a b ha hb : Measure ℕ)) =
      Real.exp (a * (Real.exp t - 1) + b * (Real.exp ((j : ℝ) * t) - 1)) := by
  have hs := hasSum_law_exp j a b t ha hb
  have hi : Integrable (fun k : ℕ ↦ Real.exp (t * k)) (law j a b ha hb : Measure ℕ) := by
    apply (AtomicTests.integrable_iff_summable _ _).mpr
    simpa only [abs_of_pos (Real.exp_pos _)] using hs.summable
  rw [← AtomicTests.expectation_eq_integral _ _ hi]
  exact hs.tsum_eq

theorem integral_hermite_exp (μ α t : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) :
    (∫ k : ℕ, Real.exp (t * k) ∂(HermiteReference.law μ α hα hαμ : Measure ℕ)) =
      Real.exp (μ * (Real.exp t - 1) + (α / 2) * (Real.exp t - 1) ^ 2) := by
  have hs := hasSum_hermite_exp μ α t hα hαμ
  have hi : Integrable (fun k : ℕ ↦ Real.exp (t * k)) (HermiteReference.law μ α hα hαμ : Measure ℕ) := by
    apply (AtomicTests.integrable_iff_summable _ _).mpr
    simpa only [abs_of_pos (Real.exp_pos _)] using hs.summable
  rw [← AtomicTests.expectation_eq_integral _ _ hi]
  exact hs.tsum_eq

end PaperP1.CompoundPoissonMoments
