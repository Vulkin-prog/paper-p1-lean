module

public import PaperP1.Probability.PositionalDeterministicMap

/-! # Compose actual field kernels with a deterministic input transformation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalKernelComposition

open PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCoefficientExpansion
  PaperP1.PositionalMarkovKernel PaperP1.PositionalDeterministicMap
  PaperP1.PositivePositionalConvolution

variable {ι κ τ : Type*}

theorem action_push (K : Configuration κ → Space τ) (hK : ∀ v, IsProbability (K v))
    (f : Configuration ι → Configuration κ) (ν : Space ι) :
    action K hK (push f ν) = action (fun v ↦ K (f v)) (fun v ↦ hK (f v)) ν := by
  have hh := ((hasSum_coeff_atoms ν).map (push f) (push f).continuous).map
    (action K hK) (action K hK).continuous
  simp only [Function.comp_def, map_smul, push_atom, action_atom] at hh
  exact hh.tsum_eq.symm

theorem push_comp (g : Configuration κ → Configuration τ)
    (f : Configuration ι → Configuration κ) (ν : Space ι) :
    push g (push f ν) = push (g ∘ f) ν := action_push _ _ f ν

theorem push_shift (a : Configuration ι) (ν : Space ι) :
    push (fun v ↦ v + a) ν = ofFinite (atom a) * ν := by
  have hpush := (hasSum_coeff_atoms ν).map (push (fun v ↦ v + a))
    (push (fun v ↦ v + a)).continuous
  simp only [Function.comp_def, map_smul, push_atom] at hpush
  have hmul := HasSum.mul_left (ofFinite (atom a)) (hasSum_coeff_atoms ν)
  have hterm (v : Configuration ι) :
      ofFinite (atom a) * (coeff v ν • ofFinite (atom v)) =
        coeff v ν • ofFinite (atom (v + a)) := by
    rw [mul_smul_comm, ← map_mul, atom_mul, add_comm]
  simp_rw [hterm] at hmul
  exact hpush.unique hmul

end PaperP1.PositionalKernelComposition
