module

public import PaperP1.Probability.PositionalCountTests
public import PaperP1.Probability.PositionalCountReference
public import PaperP1.Probability.HermitePolynomialMoments

/-! # Uniform polynomial moments of the positive full positional reference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalReferenceMoments

open Finset PaperP1.PositionalFiniteLaw PaperP1.PositionalCountProjection
  PaperP1.PositionalCompoundPoisson PaperP1.CompletedPositionalLaw

variable {ι : Type*}

theorem uniform_bound (M : ℝ) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (G : Finset ι) (E : Finset (Finset ι))
      (p : ι → ℝ) (q : Finset ι → ℝ),
      (∀ e ∈ E, e ⊆ G ∧ e.card = 2) →
      (∀ x ∈ G, 0 ≤ p x - incidence E q x) →
      (∀ e ∈ E, 0 ≤ q e) → (∑ x ∈ G, p x) ≤ M →
      Summable (fun v ↦ coeff v (target G E p q) * (1 + (totalCount v : ℝ)) ^ r) ∧
      (∑' v, coeff v (target G E p q) * (1 + (totalCount v : ℝ)) ^ r) ≤ B := by
  obtain ⟨B, hB, hmoment⟩ := HermitePolynomialMoments.uniform_bound M r
  refine ⟨B, hB, ?_⟩
  intro G E p q hE hp hq hmean
  let μ := ∑ x ∈ G, p x
  let α := 2 * ∑ e ∈ E, q e
  have hα : 0 ≤ α := mul_nonneg (by norm_num) (sum_nonneg hq)
  have hαμ : α ≤ μ := PositionalCountReference.parameter_admissible G E p q hE hp
  have hh := hmoment μ α hα hαμ hmean
  have hcoeff (k : ℕ) : CompletedLaw.coeff k (projection (target G E p q)) =
      AtomicProbability.realMass (HermiteReference.law μ α hα hαμ) k := by
    rw [PositionalCountReference.projection_target G E p q hE]
    exact HermiteReference.coeff_law μ α hα hαμ k
  have hnonneg := (target_isProbability G E p q hp hq).1
  have hs : Summable (fun k : ℕ ↦
      CompletedLaw.coeff k (projection (target G E p q)) * (1 + (k : ℝ)) ^ r) := by
    simpa only [hcoeff] using hh.1
  have hfield := PositionalCountTests.summable_test (target G E p q) hnonneg
    (fun k ↦ (1 + (k : ℝ)) ^ r) (fun k ↦ by positivity) hs
  have he := PositionalCountTests.test_eq (target G E p q) hnonneg
    (fun k ↦ (1 + (k : ℝ)) ^ r) (fun k ↦ by positivity) hs
  simp only [hcoeff] at he
  exact ⟨hfield, he.trans_le hh.2⟩

end PaperP1.PositionalReferenceMoments
