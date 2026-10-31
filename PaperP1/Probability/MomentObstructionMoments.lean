module

public import PaperP1.Probability.MomentObstructionMass

/-! # Actual factorial moments of the positive perturbation

An exponential bound proves integrability at every factorial order. The
finite signed perturbation is then integrated exactly, rather than using
totalized expectations of a potentially nonintegrable observable.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MomentObstructionMoments

open MeasureTheory PaperP1.Probability PaperP1.PoissonSequence PaperP1.PoissonExponential
  PaperP1.DifferenceCoefficients PaperP1.MomentObstructionMass PaperP1.AtomicProbability Finset

theorem hasSum_qMass_exp (a t : ℝ) :
    HasSum (fun k : ℕ ↦ qMass a k * Real.exp (t * k))
      (Real.exp (Real.exp t - 1) * (1 + a / 2 * (Real.exp t - 1) ^ 2)) := by
  simpa only [qMass, one_mul] using hasSum_quadraticMass_exp 1 a t

theorem hasSum_pMass_weighted (m : ℕ) (a : ℝ) (f : ℕ → ℝ) {s : ℝ}
    (hq : HasSum (fun k ↦ qMass a k * f k) s) :
    HasSum (fun k ↦ pMass m a k * f k)
      (s + epsilon m a * ∑ k ∈ ((forwardDifference : SignedLaw ℝ) ^ m).coeff.support,
        ((forwardDifference : SignedLaw ℝ) ^ m).coeff k * f k) := by
  have hd := hasSum_weighted_finite ((forwardDifference : SignedLaw ℝ) ^ m) f
  have h := hq.add (hd.mul_left (epsilon m a))
  convert h using 1
  funext k
  unfold pMass
  ring

theorem qMass_factorial_summable (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (j : ℕ) :
    Summable (fun k ↦ qMass a k * (k.descFactorial j : ℝ)) := by
  have h := (hasSum_qMass_exp a 1).summable
  simp only [one_mul] at h
  exact summable_factorial_of_exp (qMass_nonneg a ha0 ha2) h j

theorem integral_difference (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (f : ℕ → ℝ) (hf : Summable (fun k ↦ qMass a k * f k)) :
    (∫ k, f k ∂(pLaw m hm a ha0 ha2 : Measure ℕ)) -
      (∫ k, f k ∂(qLaw a ha0 ha2 : Measure ℕ)) =
        epsilon m a * ∑ k ∈ ((forwardDifference : SignedLaw ℝ) ^ m).coeff.support,
          ((forwardDifference : SignedLaw ℝ) ^ m).coeff k * f k := by
  change (∫ k, f k ∂(ofMass _ _ _ : Measure ℕ)) - (∫ k, f k ∂(ofMass _ _ _ : Measure ℕ)) = _
  rw [ofMass_integral, ofMass_integral]
  have h := (hasSum_pMass_weighted m a f hf.hasSum).tsum_eq
  linarith

theorem qLaw_factorial_integrable (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (j : ℕ) :
    Integrable (fun k : ℕ ↦ (k.descFactorial j : ℝ)) (qLaw a ha0 ha2 : Measure ℕ) := by
  apply (ofMass_integrable_iff _ _ _ _).mpr
  simpa only [Nat.abs_cast] using qMass_factorial_summable a ha0 ha2 j

theorem pLaw_factorial_integrable (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (j : ℕ) : Integrable (fun k : ℕ ↦ (k.descFactorial j : ℝ)) (pLaw m hm a ha0 ha2 : Measure ℕ) := by
  apply (ofMass_integrable_iff _ _ _ _).mpr
  have h := (hasSum_pMass_weighted m a (fun k ↦ (k.descFactorial j : ℝ))
    (qMass_factorial_summable a ha0 ha2 j).hasSum).summable
  simpa only [Nat.abs_cast] using h

theorem factorial_moment_difference (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) (j : ℕ) :
    (∫ k, (k.descFactorial j : ℝ) ∂(pLaw m hm a ha0 ha2 : Measure ℕ)) -
      (∫ k, (k.descFactorial j : ℝ) ∂(qLaw a ha0 ha2 : Measure ℕ)) =
        epsilon m a * (if m = j then (m.factorial : ℝ) else 0) := by
  rw [integral_difference m hm a ha0 ha2 _ (qMass_factorial_summable a ha0 ha2 j),
    difference_factorial_moment]

theorem factorial_moment_eq_of_ne (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) (j : ℕ) (hjm : j ≠ m) :
    (∫ k, (k.descFactorial j : ℝ) ∂(pLaw m hm a ha0 ha2 : Measure ℕ)) =
      ∫ k, (k.descFactorial j : ℝ) ∂(qLaw a ha0 ha2 : Measure ℕ) := by
  have h := factorial_moment_difference m hm a ha0 ha2 j
  rw [ite_eq_right (Ne.symm hjm), mul_zero] at h
  exact sub_eq_zero.mp h

theorem factorial_moment_changed_order (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) :
    (∫ k, (k.descFactorial m : ℝ) ∂(pLaw m hm a ha0 ha2 : Measure ℕ)) -
      (∫ k, (k.descFactorial m : ℝ) ∂(qLaw a ha0 ha2 : Measure ℕ)) = sourceConstant a / 2 := by
  rw [factorial_moment_difference, ite_eq_left rfl, epsilon_mul_factorial]

theorem factorial_moment_eq_iff (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) (ha : a < 2) (j : ℕ) :
    ((∫ k, (k.descFactorial j : ℝ) ∂(pLaw m hm a ha0 ha2 : Measure ℕ)) =
      ∫ k, (k.descFactorial j : ℝ) ∂(qLaw a ha0 ha2 : Measure ℕ)) ↔ j ≠ m := by
  constructor
  · intro heq hjm
    subst j
    have h := factorial_moment_changed_order m hm a ha0 ha2
    rw [heq, sub_self] at h
    have hpos := sourceConstant_pos a ha
    linarith
  · exact factorial_moment_eq_of_ne m hm a ha0 ha2 j

end PaperP1.MomentObstructionMoments
