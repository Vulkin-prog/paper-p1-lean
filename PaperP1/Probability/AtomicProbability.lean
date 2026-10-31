module

public import PaperP1.Probability.AtomicSignedLaw
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # Canonical actual probability measures from normalized real masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AtomicProbability

open MeasureTheory

/-- The probability convention: half the ordinary sum of absolute singleton differences. -/
def totalVariation (μ ν : ProbabilityMeasure ℕ) : ℝ :=
  (∑' k : ℕ, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|) / 2

def realMass (μ : ProbabilityMeasure ℕ) (k : ℕ) : ℝ := (μ : Measure ℕ).real {k}

theorem realMass_nonneg (μ : ProbabilityMeasure ℕ) (k : ℕ) : 0 ≤ realMass μ k := measureReal_nonneg

theorem hasSum_realMass (μ : ProbabilityMeasure ℕ) : HasSum (realMass μ) 1 := by
  have hs : (∑' k : ℕ, (μ : Measure ℕ) {k}) = 1 := (μ : Measure ℕ).toPMF.tsum_coe
  have htop : (∑' k : ℕ, (μ : Measure ℕ) {k}) ≠ ⊤ := by rw [hs]; exact ENNReal.one_ne_top
  have h := ENNReal.hasSum_toReal htop
  have hr : (∑' k : ℕ, ((μ : Measure ℕ) {k}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k ↦ measure_ne_top (μ : Measure ℕ) {k}), hs]
    simp
  rw [hr] at h
  exact h

theorem totalVariation_nonneg (μ ν : ProbabilityMeasure ℕ) : 0 ≤ totalVariation μ ν :=
  div_nonneg (tsum_nonneg fun _ ↦ abs_nonneg _) (by norm_num)

theorem totalVariation_symm (μ ν : ProbabilityMeasure ℕ) : totalVariation μ ν = totalVariation ν μ := by
  unfold totalVariation
  congr 1
  apply tsum_congr
  intro k
  exact abs_sub_comm _ _

@[simp] theorem totalVariation_self (μ : ProbabilityMeasure ℕ) : totalVariation μ μ = 0 := by
  simp [totalVariation]

def ofMass (a : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ a k) (ha : HasSum a 1) : ProbabilityMeasure ℕ :=
  ⟨Measure.sum (fun k ↦ ENNReal.ofReal (a k) • Measure.dirac k),
    ha.isProbabilityMeasure_sum_dirac hnonneg⟩

theorem ofMass_real_singleton (a : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ a k)
    (ha : HasSum a 1) (k : ℕ) : (ofMass a hnonneg ha : Measure ℕ).real {k} = a k := by
  change ((Measure.sum (fun k ↦ ENNReal.ofReal (a k) • Measure.dirac k)) {k}).toReal = a k
  rw [Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hnonneg k)]

theorem ofMass_integrable_iff (a : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ a k)
    (ha : HasSum a 1) (f : ℕ → ℝ) :
    Integrable f (ofMass a hnonneg ha : Measure ℕ) ↔ Summable (fun k ↦ a k * |f k|) := by
  change Integrable f (Measure.sum (fun k ↦ ENNReal.ofReal (a k) • Measure.dirac k)) ↔ _
  rw [integrable_sum_dirac_iff (by simp)]
  simp only [ENNReal.toReal_ofReal (hnonneg _), Real.norm_eq_abs]

theorem ofMass_integral (a : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ a k)
    (ha : HasSum a 1) (f : ℕ → ℝ) :
    (∫ k, f k ∂(ofMass a hnonneg ha : Measure ℕ)) = ∑' k, a k * f k := by
  change (∫ k, f k ∂Measure.sum (fun k ↦ ENNReal.ofReal (a k) • Measure.dirac k)) = _
  rw [integral_sum_dirac (by simp)]
  simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul]

theorem ofMass_toSignedMeasure (a : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ a k)
    (ha : HasSum a 1) :
    (ofMass a hnonneg ha : Measure ℕ).toSignedMeasure = AtomicSignedLaw.ofSequence a := by
  apply AtomicSignedLaw.signedMeasure_ext_singleton
  intro k
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k), ofMass_real_singleton,
    AtomicSignedLaw.ofSequence_singleton ha.summable k]

end PaperP1.AtomicProbability
