module

public import PaperP1.Probability.AtomicTests
public import PaperP1.Probability.PoissonSteinSolution

/-! # The unweighted signed recurrence and its exact test identity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawRecurrence

open MeasureTheory PaperP1.AtomicProbability PaperP1.AtomicTests PaperP1.PoissonSequence

def FiniteFirstMoment (P : ProbabilityMeasure ℕ) : Prop := Summable (fun k : ℕ ↦ (k : ℝ) * realMass P k)

def firstMoment (P : ProbabilityMeasure ℕ) : ℝ := ∑' k : ℕ, (k : ℝ) * realMass P k

def residual (P : ProbabilityMeasure ℕ) (μ θ : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * realMass P k - (μ - θ) * shift (realMass P) k - θ * shift (shift (realMass P)) k

def norm (P : ProbabilityMeasure ℕ) (μ θ : ℝ) : ℝ := ∑' k : ℕ, |residual P μ θ k|

def operator (μ θ : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  μ * f (k + 1) + θ * (f (k + 2) - f (k + 1)) - (k : ℝ) * f k

theorem summable_residual (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P) (μ θ : ℝ) :
    Summable (residual P μ θ) :=
  (hP.sub ((hasSum_shift (hasSum_realMass P)).summable.mul_left (μ - θ))).sub
    ((hasSum_shift (hasSum_shift (hasSum_realMass P))).summable.mul_left θ)

theorem norm_nonneg (P : ProbabilityMeasure ℕ) (μ θ : ℝ) : 0 ≤ norm P μ θ :=
  tsum_nonneg (fun _ ↦ abs_nonneg _)

theorem shifted_test_sum {a : ℕ → ℝ} (ha : Summable a) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    (∑' k, shift a k * f k) = ∑' k, a k * f (k + 1) := by
  have hs := hasSum_shift (summable_mul_unit ha (fun k ↦ hf (k + 1))).hasSum
  have heq : shift (fun k ↦ a k * f (k + 1)) = (fun k ↦ shift a k * f k) := by
    funext k
    cases k <;> simp
  rw [heq] at hs
  exact hs.tsum_eq

theorem operator_summable (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (μ θ : ℝ) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    Summable (fun k ↦ realMass P k * operator μ θ f k) := by
  have hp := (hasSum_realMass P).summable
  have h1 := summable_mul_unit hp (fun k ↦ hf (k + 1))
  have h2 := summable_mul_unit hp (fun k ↦ hf (k + 2))
  have h3 := summable_mul_unit hP hf
  convert ((h1.mul_left μ).add ((h2.sub h1).mul_left θ)).sub h3 using 1
  funext k
  unfold operator
  ring

theorem operator_expectation (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (μ θ : ℝ) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    expectation P (operator μ θ f) = -(∑' k, residual P μ θ k * f k) := by
  have hp := (hasSum_realMass P).summable
  have hs1 := (hasSum_shift (hasSum_realMass P)).summable
  have hs2 := (hasSum_shift (hasSum_shift (hasSum_realMass P))).summable
  have h0 := summable_mul_unit hP hf
  have h1 := summable_mul_unit hs1 hf
  have h2 := summable_mul_unit hs2 hf
  have hr : (∑' k, residual P μ θ k * f k) =
      (∑' k : ℕ, ((k : ℝ) * realMass P k) * f k) -
      (μ - θ) * (∑' k, shift (realMass P) k * f k) -
      θ * (∑' k, shift (shift (realMass P)) k * f k) := by
    have heq : (fun k ↦ residual P μ θ k * f k) = fun k : ℕ ↦
        ((k : ℝ) * realMass P k) * f k - (μ - θ) * (shift (realMass P) k * f k) -
          θ * (shift (shift (realMass P)) k * f k) := by
      funext k
      unfold residual
      ring
    rw [heq, (h0.sub (h1.mul_left (μ - θ))).tsum_sub (h2.mul_left θ),
      h0.tsum_sub (h1.mul_left (μ - θ)), tsum_mul_left, tsum_mul_left]
  rw [hr, shifted_test_sum hp f hf, shifted_test_sum hs1 f hf,
    shifted_test_sum hp (fun k ↦ f (k + 1)) (fun k ↦ hf (k + 1))]
  have hp1 := summable_mul_unit hp (fun k ↦ hf (k + 1))
  have hp2 := summable_mul_unit hp (fun k ↦ hf (k + 2))
  unfold expectation
  have hrew : (fun k ↦ realMass P k * operator μ θ f k) = fun k ↦
      μ * (realMass P k * f (k + 1)) + θ * (realMass P k * f (k + 2) - realMass P k * f (k + 1)) -
        ((k : ℝ) * realMass P k) * f k := by
    funext k
    unfold operator
    ring
  rw [hrew, ((hp1.mul_left μ).add ((hp2.sub hp1).mul_left θ)).tsum_sub h0,
    (hp1.mul_left μ).tsum_add ((hp2.sub hp1).mul_left θ), tsum_mul_left, tsum_mul_left,
    hp2.tsum_sub hp1]
  simp only [Nat.add_assoc]
  ring

theorem operator_expectation_bound (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (μ θ : ℝ) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    |expectation P (operator μ θ f)| ≤ norm P μ θ := by
  rw [operator_expectation P hP μ θ f hf, abs_neg]
  exact abs_tsum_mul_unit (summable_residual P hP μ θ) hf

theorem stein_expectation {μ : ℝ} (hμ : 0 < μ) (P : ProbabilityMeasure ℕ)
    (θ : ℝ) (h : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k ∧ h k ≤ 1) :
    expectation P (operator μ θ (PoissonSteinSolution.solution μ h)) =
      expectation P h - PoissonSteinSolution.mean μ h + θ *
        expectation P (fun k ↦ PoissonSteinSolution.solution μ h (k + 2) - PoissonSteinSolution.solution μ h (k + 1)) := by
  let f := PoissonSteinSolution.solution μ h
  let m := PoissonSteinSolution.mean μ h
  have htest : ∀ k, |h k| ≤ 1 := fun k ↦ by rw [abs_of_nonneg (hh k).1]; exact (hh k).2
  have hp := (hasSum_realMass P).summable
  have hhS := summable_mul_unit hp htest
  have hdelta := summable_mul_unit hp (fun k ↦ PoissonSteinSolution.solution_difference_abs_le_one hμ hh (k + 1))
  have hfun : (fun k ↦ realMass P k * operator μ θ f k) =
      fun k ↦ realMass P k * h k - m * realMass P k +
        θ * (realMass P k * (f (k + 2) - f (k + 1))) := by
    funext k
    have heq := PoissonSteinSolution.stein_equation hμ h k
    change μ * f (k + 1) - (k : ℝ) * f k = h k - m at heq
    have hprod := congrArg (fun z : ℝ ↦ realMass P k * z) heq
    unfold operator
    nlinarith
  change (∑' k, realMass P k * operator μ θ f k) = _
  rw [hfun, (hhS.sub (hp.mul_left m)).tsum_add (hdelta.mul_left θ), hhS.tsum_sub (hp.mul_left m),
    tsum_mul_left, tsum_mul_left, (hasSum_realMass P).tsum_eq, mul_one]
  rfl

/-- A conditional interface only: the reference's stationarity must still be proved. -/
theorem comparison_of_stationary (P Q : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθhalf : θ < 1 / 2)
    (hQ : ∀ f : ℕ → ℝ, (∀ k, |f k| ≤ 1) → expectation Q (operator μ θ f) = 0) :
    totalVariation P Q ≤ norm P μ θ / (1 - 2 * θ) := by
  have hden : 0 < 1 - 2 * θ := by linarith
  let h := attainingTest P Q
  let f := PoissonSteinSolution.solution μ h
  have hh := attainingTest_bounds P Q
  have hf := PoissonSteinSolution.solution_abs_le_one hμ hh
  have hp := stein_expectation hμ P θ h hh
  have hq := stein_expectation hμ Q θ h hh
  rw [hQ f hf] at hq
  have hTV := attainingTest_difference P Q
  have hbound := operator_expectation_bound P hP μ θ f hf
  have hdelta := unit_expectation_difference P Q (fun k ↦ f (k + 2) - f (k + 1))
    (fun k ↦ PoissonSteinSolution.solution_difference_abs_le_one hμ hh (k + 1))
  have hupper := (abs_le.mp hbound).2
  have hlower := (abs_le.mp hdelta).1
  apply (le_div_iff₀ hden).mpr
  change expectation P h - expectation Q h = totalVariation P Q at hTV
  nlinarith

end PaperP1.RawRecurrence
