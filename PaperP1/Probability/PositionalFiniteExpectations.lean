module

public import PaperP1.Probability.PositionalDeterministicMap

/-! # Arbitrary real tests of finite mixtures of counting fields -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalFiniteExpectations

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.FiniteConvolutionAlgebra

variable {ι Ω : Type*} [Fintype Ω]

theorem hasSum_mixture (a : Ω → ℝ) (K : Ω → Space ι)
    (f : Configuration ι → ℝ) (t : Ω → ℝ)
    (ht : ∀ ω, HasSum (fun v ↦ coeff v (K ω) * f v) (t ω)) :
    HasSum (fun v ↦ coeff v (∑ ω, a ω • K ω) * f v) (∑ ω, a ω * t ω) := by
  have hh := hasSum_sum (s := univ) (fun ω _ ↦ (ht ω).mul_left (a ω))
  convert hh using 1
  funext v
  simp only [map_sum, map_smul, smul_eq_mul, sum_mul, mul_assoc]

theorem law_eq_mixture (G : Finset ι) (a : Ω → ℝ) (J : ι → Ω → Bool) :
    ofFinite (law G a J) = ∑ ω, a ω • ofFinite (atom (configuration G J ω)) := by
  rw [law, map_sum]
  apply sum_congr rfl
  intro ω _
  rw [map_mul]
  change algebraMap ℝ (Space ι) (a ω) * _ = _
  rw [Algebra.smul_def]

theorem hasSum_law (G : Finset ι) (a : Ω → ℝ) (J : ι → Ω → Bool)
    (f : Configuration ι → ℝ) :
    HasSum (fun v ↦ coeff v (ofFinite (law G a J)) * f v)
      (∑ ω, a ω * f (configuration G J ω)) := by
  rw [law_eq_mixture]
  exact hasSum_mixture a _ f _ (fun ω ↦ PositionalDeterministicMap.hasSum_atom_test _ f)

end PaperP1.PositionalFiniteExpectations
