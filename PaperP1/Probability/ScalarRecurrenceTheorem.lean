module

public import PaperP1.Probability.SizeBiasedRecurrence
public import PaperP1.Analysis.WeightedRecurrence

/-! # Companion T19.11, with closed unit Stein bounds and actual reference laws -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarRecurrenceTheorem

open MeasureTheory PaperP1.AtomicProbability PaperP1.AtomicTests PaperP1.PoissonSequence
  PaperP1.RawRecurrence PaperP1.HermiteRecurrence PaperP1.SizeBiasedRecurrence

theorem finiteFirstMoment_iff_integrable (P : ProbabilityMeasure ℕ) :
    FiniteFirstMoment P ↔ Integrable (fun k : ℕ ↦ (k : ℝ)) (P : Measure ℕ) := by
  rw [integrable_iff_summable]
  have heq : (fun k : ℕ ↦ realMass P k * |(k : ℝ)|) = fun k : ℕ ↦ (k : ℝ) * realMass P k := by
    funext k
    rw [abs_of_nonneg (Nat.cast_nonneg k), mul_comm]
  rw [heq]
  rfl

theorem firstMoment_eq_integral (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P) :
    firstMoment P = ∫ k : ℕ, (k : ℝ) ∂(P : Measure ℕ) := by
  have h := expectation_eq_integral P (fun k : ℕ ↦ (k : ℝ)) ((finiteFirstMoment_iff_integrable P).mp hP)
  simpa only [firstMoment, expectation, mul_comm] using h

theorem residual_parameter_bound (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P) (μ θ ν κ : ℝ) :
    |RawRecurrence.norm P μ θ - RawRecurrence.norm P ν κ| ≤ |μ - ν| + 2 * |θ - κ| := by
  have hr := WeightedRecurrence.abs_l1_sub_le (summable_residual P hP μ θ) (summable_residual P hP ν κ)
  have hs1 := hasSum_shift (hasSum_realMass P)
  have hs2 := hasSum_shift hs1
  have hshift0 : ∀ k, 0 ≤ shift (realMass P) k := by intro k; cases k <;> simp [realMass_nonneg]
  have hshift20 : ∀ k, 0 ≤ shift (shift (realMass P)) k := by intro k; cases k <;> simp [hshift0]
  have hmajor := (hs1.mul_left |μ - ν|).add ((hs1.add hs2).mul_left |θ - κ|)
  have hterm : ∀ k, |residual P μ θ k - residual P ν κ k| ≤
      |μ - ν| * shift (realMass P) k + |θ - κ| * (shift (realMass P) k + shift (shift (realMass P)) k) := by
    intro k
    have heq : residual P μ θ k - residual P ν κ k =
        (ν - μ) * shift (realMass P) k + (θ - κ) * (shift (realMass P) k - shift (shift (realMass P)) k) := by
      unfold RawRecurrence.residual
      ring
    rw [heq]
    have ht := abs_add_le ((ν - μ) * shift (realMass P) k)
      ((θ - κ) * (shift (realMass P) k - shift (shift (realMass P)) k))
    rw [abs_mul, abs_mul, abs_sub_comm ν μ, abs_of_nonneg (hshift0 k)] at ht
    have hdiff := abs_sub (shift (realMass P) k) (shift (shift (realMass P)) k)
    rw [abs_of_nonneg (hshift0 k), abs_of_nonneg (hshift20 k)] at hdiff
    have hm := mul_le_mul_of_nonneg_left hdiff (abs_nonneg (θ - κ))
    linarith
  have hsum := hasSum_le hterm
    ((summable_residual P hP μ θ).sub (summable_residual P hP ν κ)).abs.hasSum hmajor
  change |RawRecurrence.norm P μ θ - RawRecurrence.norm P ν κ| ≤ _ at hr
  unfold WeightedRecurrence.l1 at hr
  simp only [Pi.sub_apply] at hr
  simp only [mul_one, one_add_one_eq_two] at hsum
  nlinarith

/-- Both numbered conclusions; the size-bias identity is proved for every permitted parameter. -/
theorem companion_T19_11 :
    (∀ (P : ProbabilityMeasure ℕ), FiniteFirstMoment P → ∀ μ θ : ℝ,
      ∀ hθ : 0 ≤ θ, ∀ hbound : θ < min μ (1 / 2),
        totalVariation P (reference μ θ hθ (lt_min_iff.mp hbound).1.le) ≤
          RawRecurrence.norm P μ θ / (1 - 2 * θ)) ∧
    (∀ (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P) (hm : 0 < firstMoment P) (κ : ℝ),
      ∀ hκ : 0 ≤ κ, ∀ hbound : κ < min (firstMoment P) (1 / 2),
        RawRecurrence.norm P (firstMoment P) κ = 2 * firstMoment P *
          totalVariation (sizeBiased P hP hm)
            (shiftMixture P (firstMoment P) κ hm hκ (lt_min_iff.mp hbound).1.le)) := by
  constructor
  · intro P hP μ θ hθ hbound
    exact scalar_recurrence_criterion P hP hθ (lt_min_iff.mp hbound).1 (lt_min_iff.mp hbound).2
  · intro P hP hm κ hκ hbound
    exact size_bias_totalVariation_identity P hP hm hκ (lt_min_iff.mp hbound).1.le

end PaperP1.ScalarRecurrenceTheorem
