module

public import PaperP1.Probability.AtomicSignedLaw
public import PaperP1.Probability.FiniteLawShift

/-! # Finite count laws as actual summable atomic signed measures -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteLawEmbedding

open MeasureTheory PaperP1.Probability PaperP1.AtomicSignedLaw

theorem summable_coeff (ν : SignedLaw ℝ) : Summable ν.coeff :=
  summable_of_hasFiniteSupport ν.coeff.hasFiniteSupport

theorem l1Norm_eq_tsum (ν : SignedLaw ℝ) : l1Norm ν = ∑' k : ℕ, |ν.coeff k| := by
  unfold l1Norm Finsupp.sum
  symm
  apply tsum_eq_sum
  intro k hk
  rw [Finsupp.notMem_support_iff.mp hk, abs_zero]

def embed (ν : SignedLaw ℝ) : SignedMeasure ℕ := ofSequence ν.coeff

theorem embed_singleton (ν : SignedLaw ℝ) (k : ℕ) : embed ν {k} = ν.coeff k :=
  ofSequence_singleton (summable_coeff ν) k

theorem tsum_coeff_eq_mass (ν : SignedLaw ℝ) : (∑' k : ℕ, ν.coeff k) = totalMass ν := by
  rw [totalMass_eq_sum_coeff]
  exact tsum_eq_sum fun k hk ↦ Finsupp.notMem_support_iff.mp hk

theorem embed_univ (ν : SignedLaw ℝ) : embed ν Set.univ = totalMass ν := by
  rw [embed, ofSequence_univ (summable_coeff ν), tsum_coeff_eq_mass]

theorem embed_isProbability {ν : SignedLaw ℝ} (hν : Probability.IsProbability ν) :
    AtomicSignedLaw.IsProbability (embed ν) := by
  have hs : HasSum ν.coeff 1 := by
    have h := (summable_coeff ν).hasSum
    rwa [tsum_coeff_eq_mass, hν.2] at h
  exact (isProbability_ofSequence_iff hs).mpr hν.1

theorem embed_injective : Function.Injective embed := by
  intro μ ν h
  ext k
  rw [← embed_singleton, ← embed_singleton, h]

theorem embed_add (μ ν : SignedLaw ℝ) : embed (μ + ν) = embed μ + embed ν := by
  apply signedMeasure_ext_singleton
  intro k
  rw [embed_singleton, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, _root_.add_apply,
    embed_singleton, embed_singleton]

theorem embed_sub (μ ν : SignedLaw ℝ) : embed (μ - ν) = embed μ - embed ν := by
  apply signedMeasure_ext_singleton
  intro k
  rw [embed_singleton, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, _root_.sub_apply,
    embed_singleton, embed_singleton]

theorem embed_scalar_mul (c : ℝ) (ν : SignedLaw ℝ) : embed (scalar c * ν) = c • embed ν := by
  apply signedMeasure_ext_singleton
  intro k
  rw [embed_singleton, PaperP1.FiniteLawShift.scalar_mul_coeff, _root_.smul_apply,
    embed_singleton, smul_eq_mul]

theorem l1Norm_eq_signed_singleton_tsum (ν : SignedLaw ℝ) :
    l1Norm ν = ∑' k : ℕ, |embed ν {k}| := by
  simp only [embed_singleton]
  exact l1Norm_eq_tsum ν

end PaperP1.FiniteLawEmbedding
