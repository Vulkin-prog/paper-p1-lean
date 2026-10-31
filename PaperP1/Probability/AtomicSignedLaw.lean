module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Summable singleton masses as actual signed measures on the naturals

Integrability is always proved before using the density construction.
Consequently its totalized zero case cannot hide an infinite-mass sequence.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AtomicSignedLaw

open MeasureTheory

def ofSequence (a : ℕ → ℝ) : SignedMeasure ℕ := Measure.count.withDensityᵥ a

theorem integrable_of_summable {a : ℕ → ℝ} (ha : Summable a) :
    Integrable a Measure.count := integrable_count_iff.mpr ha.norm

theorem ofSequence_singleton {a : ℕ → ℝ} (ha : Summable a) (k : ℕ) :
    ofSequence a {k} = a k := by
  rw [ofSequence, withDensityᵥ_apply (integrable_of_summable ha) (measurableSet_singleton k)]
  simp

theorem ofSequence_univ {a : ℕ → ℝ} (ha : Summable a) :
    ofSequence a Set.univ = ∑' k, a k := by
  rw [ofSequence, withDensityᵥ_apply (integrable_of_summable ha) MeasurableSet.univ,
    setIntegral_univ, integral_countable (integrable_of_summable ha)]
  simp

theorem ofSequence_add {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) :
    ofSequence (a + b) = ofSequence a + ofSequence b :=
  withDensityᵥ_add (integrable_of_summable ha) (integrable_of_summable hb)

theorem ofSequence_sub {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) :
    ofSequence (a - b) = ofSequence a - ofSequence b :=
  withDensityᵥ_sub (integrable_of_summable ha) (integrable_of_summable hb)

theorem ofSequence_smul (c : ℝ) (a : ℕ → ℝ) :
    ofSequence (c • a) = c • ofSequence a := by
  exact withDensityᵥ_smul a c

theorem signedMeasure_ext_singleton {ν κ : SignedMeasure ℕ}
    (h : ∀ k, ν {k} = κ {k}) : ν = κ := by
  apply VectorMeasure.ext
  intro s _
  have hu : (⋃ k : s, ({k.val} : Set ℕ)) = s := by ext k; simp
  have hd : Pairwise (Function.onFun Disjoint (fun k : s ↦ ({k.val} : Set ℕ))) := by
    intro i j hij
    simp only [Set.disjoint_singleton]
    exact fun heq ↦ hij (Subtype.ext heq)
  rw [← hu, VectorMeasure.of_disjoint_iUnion (v := ν)
      (f := fun k : s ↦ ({k.val} : Set ℕ)) (fun k ↦ measurableSet_singleton k.val) hd,
    VectorMeasure.of_disjoint_iUnion (v := κ)
      (f := fun k : s ↦ ({k.val} : Set ℕ)) (fun k ↦ measurableSet_singleton k.val) hd]
  exact tsum_congr fun k ↦ h k.val

def IsProbability (ν : SignedMeasure ℕ) : Prop :=
  ∃ ρ : ProbabilityMeasure ℕ, (ρ : Measure ℕ).toSignedMeasure = ν

theorem isProbability_ofSequence_iff {a : ℕ → ℝ} (ha : HasSum a 1) :
    IsProbability (ofSequence a) ↔ ∀ k, 0 ≤ a k := by
  constructor
  · rintro ⟨ρ, hρ⟩ k
    rw [← ofSequence_singleton ha.summable k, ← hρ,
      Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k)]
    exact measureReal_nonneg
  · intro hnonneg
    let ρ : Measure ℕ := Measure.sum fun k ↦ ENNReal.ofReal (a k) • Measure.dirac k
    have hρ : IsProbabilityMeasure ρ := ha.isProbabilityMeasure_sum_dirac hnonneg
    refine ⟨(⟨ρ, hρ⟩ : ProbabilityMeasure ℕ), ?_⟩
    change ρ.toSignedMeasure = ofSequence a
    apply signedMeasure_ext_singleton
    intro k
    rw [ofSequence_singleton ha.summable k,
      Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k)]
    change (ρ {k}).toReal = a k
    rw [show ρ {k} = ENNReal.ofReal (a k) from Measure.sum_smul_dirac_singleton]
    exact ENNReal.toReal_ofReal (hnonneg k)

end PaperP1.AtomicSignedLaw
