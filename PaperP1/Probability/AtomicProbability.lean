module

public import PaperP1.Probability.AtomicSignedLaw

/-! # Canonical actual probability measures from normalized real masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AtomicProbability

open MeasureTheory

/-- The probability convention: half the ordinary sum of absolute singleton differences. -/
def totalVariation (μ ν : ProbabilityMeasure ℕ) : ℝ :=
  (∑' k : ℕ, |(μ : Measure ℕ).real {k} - (ν : Measure ℕ).real {k}|) / 2

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
