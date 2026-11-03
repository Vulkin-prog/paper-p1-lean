module

public import PaperP1.Probability.AtomicProbabilityMetric
public import PaperP1.Probability.FiniteLawEmbedding

/-! # Ordinary singleton l1 distance for arbitrary actual finite signed measures on the naturals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedAtomicDistance

open MeasureTheory

def distance (μ ν : SignedMeasure ℕ) : ℝ := ∑' k : ℕ, |μ {k} - ν {k}|

theorem summable_singletons (μ : SignedMeasure ℕ) : Summable (fun k : ℕ ↦ μ {k}) := by
  have h := μ.hasSum_of_disjoint_iUnion (f := fun k : ℕ ↦ ({k} : Set ℕ))
    (fun k ↦ measurableSet_singleton k) (fun i j hij ↦ by simp only [Set.disjoint_singleton]; exact hij)
  exact h.summable

theorem nonneg (μ ν : SignedMeasure ℕ) : 0 ≤ distance μ ν := tsum_nonneg fun _k ↦ abs_nonneg _

theorem triangle (μ ν ρ : SignedMeasure ℕ) : distance μ ρ ≤ distance μ ν + distance ν ρ := by
  have hμ := summable_singletons μ
  have hν := summable_singletons ν
  have hρ := summable_singletons ρ
  have h := (hμ.sub hρ).abs.tsum_le_tsum (fun k ↦ abs_sub_le (μ {k}) (ν {k}) (ρ {k}))
    ((hμ.sub hν).abs.add (hν.sub hρ).abs)
  rw [(hμ.sub hν).abs.tsum_add (hν.sub hρ).abs] at h
  exact h

theorem probability_eq (P Q : ProbabilityMeasure ℕ) :
    distance (P : Measure ℕ).toSignedMeasure (Q : Measure ℕ).toSignedMeasure = 2 * AtomicProbability.totalVariation P Q := by
  have h := AtomicProbabilityMetric.signed_distance P Q
  simp only [_root_.sub_apply] at h
  exact h

theorem finite_eq (μ ν : Probability.SignedLaw ℝ) :
    distance (FiniteLawEmbedding.embed μ) (FiniteLawEmbedding.embed ν) = Probability.l1Norm (μ - ν) := by
  rw [FiniteLawEmbedding.l1Norm_eq_signed_singleton_tsum, FiniteLawEmbedding.embed_sub]
  rfl

end PaperP1.SignedAtomicDistance
