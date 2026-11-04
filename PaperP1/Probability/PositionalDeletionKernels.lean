module

public import PaperP1.Probability.PositionalUniformAtoms
public import PaperP1.Probability.PositionalPairDeletion

/-! # Uniform one-edge deletion and full isolation are actual field kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletionKernels

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositivePositionalConvolution
  PaperP1.PositionalCountProjection PaperP1.PositionalPairDeletion

variable {ι : Type*}

local instance deletionKernelDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def onceKernel (E : Finset (Finset ι)) (v : Configuration ι) : Space ι :=
  if (activeEdges E v).Nonempty then
    PositionalUniformAtoms.average (activeEdges E v) (fun e ↦ deleteEdge e v)
  else ofFinite (atom v)

theorem onceKernel_isProbability (E : Finset (Finset ι)) (v : Configuration ι) :
    IsProbability (onceKernel E v) := by
  unfold onceKernel
  split_ifs with h
  · exact PositionalUniformAtoms.average_isProbability _ h _
  · exact PositionalDeterministicMap.atom_isProbability v

def once (E : Finset (Finset ι)) : Space ι →L[ℝ] Space ι :=
  PositionalMarkovKernel.action (onceKernel E) (onceKernel_isProbability E)

def isolated (E : Finset (Finset ι)) : Space ι →L[ℝ] Space ι :=
  PositionalDeterministicMap.push (isolate E)

theorem once_isProbability (E : Finset (Finset ι)) (ν : Space ι) (hν : IsProbability ν) :
    IsProbability (once E ν) := PositionalMarkovKernel.action_isProbability _ _ ν hν

theorem isolated_isProbability (E : Finset (Finset ι)) (ν : Space ι) (hν : IsProbability ν) :
    IsProbability (isolated E ν) := PositionalDeterministicMap.push_isProbability _ ν hν

theorem once_contraction (E : Finset (Finset ι)) (ν μ : Space ι) :
    ‖once E ν - once E μ‖ ≤ ‖ν - μ‖ := PositionalMarkovKernel.contraction _ _ ν μ

theorem isolated_contraction (E : Finset (Finset ι)) (ν μ : Space ι) :
    ‖isolated E ν - isolated E μ‖ ≤ ‖ν - μ‖ := PositionalDeterministicMap.contraction _ ν μ

theorem onceKernel_test_summable (E : Finset (Finset ι)) (v : Configuration ι)
    (g : Configuration ι → ℝ) : Summable (fun w ↦ coeff w (onceKernel E v) * g w) := by
  unfold onceKernel
  split_ifs
  · exact (PositionalUniformAtoms.hasSum_test _ _ g).summable
  · exact (PositionalDeterministicMap.hasSum_atom_test v g).summable

theorem onceKernel_test_bound (E : Finset (Finset ι)) (v : Configuration ι)
    (g : Configuration ι → ℝ)
    (hg : ∀ e ∈ activeEdges E v, g (deleteEdge e v) ≤ g v) :
    (∑' w, coeff w (onceKernel E v) * g w) ≤ g v := by
  unfold onceKernel
  split_ifs with h
  · exact PositionalUniformAtoms.test_bound _ h _ g (g v) hg
  · exact (PositionalDeterministicMap.hasSum_atom_test v g).tsum_eq.le

theorem once_polynomial_moment_bound (E : Finset (Finset ι)) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (r : ℕ)
    (hs : Summable (fun v ↦ coeff v ν * (1 + (totalCount v : ℝ)) ^ r)) :
    Summable (fun w ↦ coeff w (once E ν) * (1 + (totalCount w : ℝ)) ^ r) ∧
      (∑' w, coeff w (once E ν) * (1 + (totalCount w : ℝ)) ^ r) ≤
        ∑' v, coeff v ν * (1 + (totalCount v : ℝ)) ^ r := by
  apply PositionalKernelMoments.test_bound _ _ ν hν _ _ (fun w ↦ by positivity) hs
    (fun v ↦ onceKernel_test_summable E v _)
  intro v
  apply onceKernel_test_bound E v _
  intro e _he
  apply pow_le_pow_left₀ (by positivity)
  have hh : (totalCount (deleteEdge e v) : ℝ) ≤ totalCount v := by
    exact_mod_cast totalCount_deleteEdge_le e v
  linarith only [hh]

theorem isolated_polynomial_moment_bound (E : Finset (Finset ι)) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (r : ℕ)
    (hs : Summable (fun v ↦ coeff v ν * (1 + (totalCount v : ℝ)) ^ r)) :
    Summable (fun w ↦ coeff w (isolated E ν) * (1 + (totalCount w : ℝ)) ^ r) ∧
      (∑' w, coeff w (isolated E ν) * (1 + (totalCount w : ℝ)) ^ r) ≤
        ∑' v, coeff v ν * (1 + (totalCount v : ℝ)) ^ r :=
  PositionalDeterministicMap.polynomial_moment_bound _ (totalCount_isolate_le E) ν hν r hs

theorem onceKernel_count_test (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e.card = 2) (f : ℕ → ℝ) :
    HasSum (fun w ↦ coeff w (onceKernel E v) * f (totalCount w)) (f (oneCount E v)) := by
  by_cases hne : (activeEdges E v).Nonempty
  · rw [onceKernel, ite_eq_left hne]
    have hs := PositionalUniformAtoms.hasSum_test (activeEdges E v)
      (fun e ↦ deleteEdge e v) (fun w ↦ f (totalCount w))
    have hcard : ((activeEdges E v).card : ℝ) ≠ 0 := by
      exact_mod_cast (card_pos.mpr hne).ne'
    have he : ((activeEdges E v).card : ℝ)⁻¹ *
        (∑ e ∈ activeEdges E v, f (totalCount (deleteEdge e v))) = f (oneCount E v) := by
      rw [oneCount, ite_eq_left hne]
      have hsum : (∑ e ∈ activeEdges E v, f (totalCount (deleteEdge e v))) =
          ∑ _e ∈ activeEdges E v, f (totalCount v - 2) :=
        sum_congr rfl (fun e he ↦ by
          rw [totalCount_deletePair E v he (hE e (mem_filter.mp he).1)])
      rw [hsum, sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    rwa [he] at hs
  · rw [onceKernel, ite_eq_right hne, oneCount, ite_eq_right hne, Nat.sub_zero]
    exact PositionalDeterministicMap.hasSum_atom_test v (fun w ↦ f (totalCount w))

end PaperP1.PositionalDeletionKernels
