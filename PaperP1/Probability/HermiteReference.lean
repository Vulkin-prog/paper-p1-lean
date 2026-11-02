module

public import PaperP1.Probability.CompoundPoissonSeries
public import PaperP1.Probability.CompletedLawShift
public import PaperP1.Analysis.BanachExponentialRemainder

/-! # The actual Hermite probability reference and its explicit quadratic error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HermiteReference

open MeasureTheory PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.JumpPoissonSeries PaperP1.CompoundPoissonSeries
  PaperP1.PoissonSequence PaperP1.BanachExponentialRemainder

def reference (μ α : ℝ) : Space := compound 2 (μ - α) (α / 2)

def law (μ α : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) : ProbabilityMeasure ℕ :=
  CompoundPoissonSeries.law 2 (μ - α) (α / 2) (sub_nonneg.mpr hαμ) (by positivity)

theorem double_generator : generator 2 = delta ^ 2 + (2 : ℝ) • delta := by
  have hatom : ofFinite (atom 2) = (ofFinite (atom 1)) ^ 2 := by
    rw [← map_pow, CompletedPoisson.atom_one_pow]
  rw [generator, hatom, delta, forwardDifference, map_sub, atom_zero, map_one, two_smul]
  ring

theorem factorization (μ α : ℝ) : reference μ α =
    poisson μ * NormedSpace.exp ((α / 2) • delta ^ 2) := by
  change NormedSpace.exp ((μ - α) • delta) * NormedSpace.exp ((α / 2) • generator 2) = _
  rw [poisson, ← NormedSpace.exp_add, ← NormedSpace.exp_add]
  congr 1
  rw [double_generator, smul_add, smul_smul]
  module

theorem actual_signed_reference (μ α : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) :
    toSignedMeasure (reference μ α) = (law μ α hα hαμ : Measure ℕ).toSignedMeasure :=
  CompoundPoissonSeries.actual_signed_measure 2 (μ - α) (α / 2) (sub_nonneg.mpr hαμ) (by positivity)

theorem coeff_law (μ α : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) (k : ℕ) :
    coeff k (reference μ α) = AtomicProbability.realMass (law μ α hα hαμ) k := by
  rw [← toSignedMeasure_singleton, actual_signed_reference μ α hα hαμ,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k)]
  rfl

theorem norm_error {μ : ℝ} (hμ : 0 ≤ μ) (α : ℝ) :
    ‖reference μ α - quadratic μ α‖ ≤ 4 * α ^ 2 * Real.exp (2 * |α|) := by
  let v := (α / 2) • delta ^ 2
  have hd : ‖delta ^ 2‖ ≤ 4 := by
    exact (norm_pow_le delta 2).trans (by nlinarith only [norm_delta_le, norm_nonneg delta])
  have hv : ‖v‖ ≤ 2 * |α| := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ |α| / 2)]
  have hid : reference μ α - quadratic μ α =
      poisson μ * (NormedSpace.exp v - (1 + v)) := by
    rw [factorization, quadratic]
    dsimp only [v]
    simp only [Algebra.smul_def]
    ring
  rw [hid]
  calc
    _ ≤ ‖poisson μ‖ * ‖NormedSpace.exp v - (1 + v)‖ := norm_mul_le _ _
    _ = ‖NormedSpace.exp v - (1 + v)‖ := by rw [norm_poisson hμ, one_mul]
    _ ≤ ‖v‖ ^ 2 * Real.exp ‖v‖ := norm_exp_sub_linear_le v
    _ ≤ (2 * |α|) ^ 2 * Real.exp (2 * |α|) := by gcongr
    _ = _ := by rw [mul_pow, sq_abs]; ring

theorem coefficient_error (μ α : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) :
    (∑' k : ℕ, |AtomicProbability.realMass (law μ α hα hαμ) k - quadraticMass μ α k|) ≤
      4 * α ^ 2 * Real.exp (2 * α) := by
  have h := (tsum_abs_coeff_le (reference μ α - quadratic μ α)).trans (norm_error (hα.trans hαμ) α)
  simpa only [map_sub, coeff_law μ α hα hαμ, coeff_quadratic, abs_of_nonneg hα] using h

/-- A finite transfer valid for any actual probability law. The count-law
approximation needed for article19.1 is a separate arithmetic obligation. -/
theorem totalVariation_transfer (P : ProbabilityMeasure ℕ) (μ α : ℝ) (hα : 0 ≤ α) (hαμ : α ≤ μ) :
    AtomicProbability.totalVariation P (law μ α hα hαμ) ≤
      (∑' k : ℕ, |AtomicProbability.realMass P k - quadraticMass μ α k|) / 2 +
        2 * α ^ 2 * Real.exp (2 * α) := by
  have hP := (AtomicProbability.hasSum_realMass P).summable
  have hH := (AtomicProbability.hasSum_realMass (law μ α hα hαμ)).summable
  have hQ := (hasSum_quadraticMass μ α (hα.trans hαμ)).summable
  have ht := (hP.sub hH).abs.tsum_le_tsum
    (fun k ↦ abs_sub_le (AtomicProbability.realMass P k) (quadraticMass μ α k)
      (AtomicProbability.realMass (law μ α hα hαμ) k)) ((hP.sub hQ).abs.add (hQ.sub hH).abs)
  rw [(hP.sub hQ).abs.tsum_add (hQ.sub hH).abs] at ht
  have he := coefficient_error μ α hα hαμ
  simp_rw [abs_sub_comm (AtomicProbability.realMass (law μ α hα hαμ) _) (quadraticMass μ α _)] at he
  unfold AtomicProbability.totalVariation
  change (∑' k, |AtomicProbability.realMass P k - AtomicProbability.realMass (law μ α hα hαμ) k|) / 2 ≤ _
  linarith only [ht, he]

end PaperP1.HermiteReference
