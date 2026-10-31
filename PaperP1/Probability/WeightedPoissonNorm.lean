module

public import PaperP1.Analysis.WeightedRecurrence
public import PaperP1.Probability.AtomicProbability

/-! # The recurrence norm for arbitrary probability laws, without a first moment

All singleton sequences and weighted residuals are proved summable. The
lower estimate uses the closed factorial resolvent, with no Stein bound
or recurrence-norm comparison passed as a hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPoissonNorm

open MeasureTheory PaperP1.WeightedRecurrence PaperP1.AtomicProbability PaperP1.PoissonSequence

def weightedNorm (P : ProbabilityMeasure ℕ) (μ : ℝ) : ℝ := l1 (residual μ (realMass P))

theorem mass_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) : 0 ≤ mass μ k := by
  unfold mass
  positivity

def poisson (μ : ℝ) (hμ : 0 ≤ μ) : ProbabilityMeasure ℕ :=
  ofMass (mass μ) (mass_nonneg μ hμ) (hasSum_mass μ hμ)

theorem poisson_eq_mathlib (μ : ℝ) (hμ : 0 ≤ μ) :
    (poisson μ hμ : Measure ℕ) = ProbabilityTheory.poissonMeasure ⟨μ, hμ⟩ := rfl

theorem realMass_poisson (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) : realMass (poisson μ hμ) k = mass μ k :=
  ofMass_real_singleton _ _ _ _

theorem weightedNorm_summable (P : ProbabilityMeasure ℕ) (μ : ℝ) :
    Summable (fun k ↦ |residual μ (realMass P) k|) := by
  simpa only [Real.norm_eq_abs] using (summable_residual μ (hasSum_realMass P).summable).norm

theorem weightedNorm_eq_raw_sum (P : ProbabilityMeasure ℕ) (μ : ℝ) :
    weightedNorm P μ = ∑' k : ℕ,
      |(k + 1 : ℝ) * realMass P (k + 1) - μ * realMass P k| / (k + 1 : ℝ) := by
  unfold weightedNorm l1
  apply tsum_congr
  intro k
  have hden : (0 : ℝ) < k + 1 := by positivity
  have heq : residual μ (realMass P) k =
      ((k + 1 : ℝ) * realMass P (k + 1) - μ * realMass P k) / (k + 1 : ℝ) := by
    unfold WeightedRecurrence.residual
    field_simp
  rw [heq, abs_div, abs_of_pos hden]

theorem realMass_l1 (P : ProbabilityMeasure ℕ) : l1 (realMass P) = 1 := by
  unfold l1
  simp_rw [abs_of_nonneg (realMass_nonneg P _)]
  exact (hasSum_realMass P).tsum_eq

theorem difference_l1 (P Q : ProbabilityMeasure ℕ) :
    l1 (realMass P - realMass Q) = 2 * totalVariation P Q := by
  unfold l1 totalVariation
  simp only [Pi.sub_apply, realMass]
  ring

theorem residual_poisson (μ : ℝ) : residual μ (mass μ) = 0 := by
  funext k
  change mass μ (k + 1) - μ / (k + 1 : ℝ) * mass μ k = 0
  rw [div_mul_eq_mul_div]
  apply sub_eq_zero.mpr
  apply (eq_div_iff (by positivity : (k + 1 : ℝ) ≠ 0)).mpr
  simpa only [Nat.cast_add, Nat.cast_one] using mass_succ_mul μ k

theorem poisson_comparison_nonnegative (P : ProbabilityMeasure ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    Real.exp (-μ) * totalVariation P (poisson μ hμ) ≤ weightedNorm P μ ∧
      weightedNorm P μ ≤ 2 * (1 + μ) * totalVariation P (poisson μ hμ) := by
  let a : ℕ → ℝ := realMass P - mass μ
  have ha : Summable a := (hasSum_realMass P).summable.sub (hasSum_mass μ hμ).summable
  have hzero : (∑' k, a k) = 0 := by
    have h := (hasSum_realMass P).sub (hasSum_mass μ hμ)
    simpa only [a, Pi.sub_apply, sub_self] using h.tsum_eq
  have hres : residual μ a = residual μ (realMass P) := by
    rw [show a = realMass P - mass μ from rfl, residual_sub, residual_poisson, sub_zero]
  have hdiff : l1 a = 2 * totalVariation P (poisson μ hμ) := by
    have hp : realMass (poisson μ hμ) = mass μ := funext (realMass_poisson μ hμ)
    change l1 (realMass P - mass μ) = _
    rw [← hp]
    exact difference_l1 P _
  have hlow := zero_mass_l1_bound μ hμ ha hzero
  have hupp := residual_l1_bound μ ha
  rw [hres, hdiff] at hlow hupp
  rw [abs_of_nonneg hμ] at hupp
  constructor
  · have h : totalVariation P (poisson μ hμ) ≤ Real.exp μ * weightedNorm P μ := by
      change 2 * totalVariation P (poisson μ hμ) ≤
        2 * Real.exp μ * weightedNorm P μ at hlow
      nlinarith
    calc
      _ ≤ Real.exp (-μ) * (Real.exp μ * weightedNorm P μ) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp
  · change weightedNorm P μ ≤ (1 + μ) * (2 * totalVariation P (poisson μ hμ)) at hupp
    nlinarith

theorem weightedNorm_stability (P Q : ProbabilityMeasure ℕ) (μ ν : ℝ) :
    |weightedNorm P μ - weightedNorm Q ν| ≤
      2 * (1 + |μ|) * totalVariation P Q + |μ - ν| := by
  have hp := (hasSum_realMass P).summable
  have hq := (hasSum_realMass Q).summable
  have h := abs_l1_sub_le (summable_residual μ hp) (summable_residual ν hq)
  rw [residual_difference] at h
  have hsum := l1_add_le (a := residual μ (realMass P - realMass Q))
    (b := fun k : ℕ ↦ (ν - μ) / (k + 1 : ℝ) * realMass Q k)
    (summable_residual μ (hp.sub hq)) (summable_weighted (ν - μ) hq)
  have hmain := residual_l1_bound μ (a := realMass P - realMass Q) (hp.sub hq)
  have hparam := weighted_l1_bound (ν - μ) hq
  rw [realMass_l1, mul_one, abs_sub_comm ν μ] at hparam
  rw [difference_l1] at hmain
  change |weightedNorm P μ - weightedNorm Q ν| ≤ _ at h
  nlinarith

theorem weightedNorm_stability_bounded (P Q : ProbabilityMeasure ℕ) (μ ν M : ℝ)
    (hμ : 0 ≤ μ) (hμM : μ ≤ M) :
    |weightedNorm P μ - weightedNorm Q ν| ≤ 2 * (1 + M) * totalVariation P Q + |μ - ν| := by
  have h := weightedNorm_stability P Q μ ν
  rw [abs_of_nonneg hμ] at h
  have htv := totalVariation_nonneg P Q
  nlinarith

/-- Original two-sided statement; the stronger result above includes μ=0. -/
theorem companion_T19_13 (P : ProbabilityMeasure ℕ) (μ : ℝ) (hμ : 0 < μ) :
    Real.exp (-μ) * totalVariation P (poisson μ hμ.le) ≤ weightedNorm P μ ∧
      weightedNorm P μ ≤ 2 * (1 + μ) * totalVariation P (poisson μ hμ.le) :=
  poisson_comparison_nonnegative P μ hμ.le

end PaperP1.WeightedPoissonNorm
