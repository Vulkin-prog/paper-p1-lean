module

public import PaperP1.Probability.PositionalDeletionKernels
public import PaperP1.Probability.PositionalWeightedKernel

/-! # Deletion and isolation contract every polynomially weighted field distance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletionWeightedContraction

open PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalCountProjection PaperP1.PositionalPairDeletion
  PaperP1.PositionalDeletionKernels

variable {ι : Type*}

theorem onceKernel_weight_le (E : Finset (Finset ι)) (v : Configuration ι) (j : ℕ) :
    (∑' w, coeff w (onceKernel E v) * (1 + (totalCount w : ℝ)) ^ j) ≤
      (1 + (totalCount v : ℝ)) ^ j := by
  apply onceKernel_test_bound E v _
  intro e _he
  apply pow_le_pow_left₀ (by positivity)
  have hh : (totalCount (deleteEdge e v) : ℝ) ≤ totalCount v := by
    exact_mod_cast totalCount_deleteEdge_le e v
  linarith only [hh]

theorem once_weighted_contraction (E : Finset (Finset ι)) (ν μ : Space ι) (j : ℕ)
    (hs : Summable (fun v ↦ (1 + (totalCount v : ℝ)) ^ j * |coeff v ν - coeff v μ|)) :
    Summable (fun w ↦ (1 + (totalCount w : ℝ)) ^ j * |coeff w (once E ν) - coeff w (once E μ)|) ∧
      (∑' w, (1 + (totalCount w : ℝ)) ^ j * |coeff w (once E ν) - coeff w (once E μ)|) ≤
        ∑' v, (1 + (totalCount v : ℝ)) ^ j * |coeff v ν - coeff v μ| := by
  have hs' : Summable (fun v ↦ |coeff v ν - coeff v μ| * (1 + (totalCount v : ℝ)) ^ j) := by
    simpa only [mul_comm] using hs
  have hh := PositionalWeightedKernel.weighted_difference_bound (onceKernel E)
    (onceKernel_isProbability E) ν μ
    (fun v ↦ (1 + (totalCount v : ℝ)) ^ j) (fun w ↦ (1 + (totalCount w : ℝ)) ^ j)
    (fun w ↦ by positivity) hs' (fun v ↦ onceKernel_test_summable E v _)
    (fun v ↦ onceKernel_weight_le E v j)
  simpa only [once, mul_comm] using hh

theorem isolated_weighted_contraction (E : Finset (Finset ι)) (ν μ : Space ι) (j : ℕ)
    (hs : Summable (fun v ↦ (1 + (totalCount v : ℝ)) ^ j * |coeff v ν - coeff v μ|)) :
    Summable (fun w ↦ (1 + (totalCount w : ℝ)) ^ j *
      |coeff w (isolated E ν) - coeff w (isolated E μ)|) ∧
      (∑' w, (1 + (totalCount w : ℝ)) ^ j * |coeff w (isolated E ν) - coeff w (isolated E μ)|) ≤
        ∑' v, (1 + (totalCount v : ℝ)) ^ j * |coeff v ν - coeff v μ| := by
  have hs' : Summable (fun v ↦ |coeff v ν - coeff v μ| * (1 + (totalCount v : ℝ)) ^ j) := by
    simpa only [mul_comm] using hs
  have hbound (v : Configuration ι) : (∑' w,
      coeff w (ofFinite (FiniteConvolutionAlgebra.atom (isolate E v))) *
        (1 + (totalCount w : ℝ)) ^ j) ≤ (1 + (totalCount v : ℝ)) ^ j := by
    rw [(PositionalDeterministicMap.hasSum_atom_test (isolate E v)
      (fun w ↦ (1 + (totalCount w : ℝ)) ^ j)).tsum_eq]
    apply pow_le_pow_left₀ (by positivity)
    have hh : (totalCount (isolate E v) : ℝ) ≤ totalCount v := by
      exact_mod_cast totalCount_isolate_le E v
    linarith only [hh]
  have hh := PositionalWeightedKernel.weighted_difference_bound
    (fun v ↦ ofFinite (FiniteConvolutionAlgebra.atom (isolate E v)))
    (fun v ↦ PositionalDeterministicMap.atom_isProbability (isolate E v)) ν μ
    (fun v ↦ (1 + (totalCount v : ℝ)) ^ j) (fun w ↦ (1 + (totalCount w : ℝ)) ^ j)
    (fun w ↦ by positivity) hs'
    (fun v ↦ (PositionalDeterministicMap.hasSum_atom_test (isolate E v) _).summable) hbound
  simpa only [isolated, PositionalDeterministicMap.push, mul_comm] using hh

end PaperP1.PositionalDeletionWeightedContraction
