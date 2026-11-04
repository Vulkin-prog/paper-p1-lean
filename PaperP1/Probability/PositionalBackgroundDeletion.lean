module

public import PaperP1.Probability.PositionalDeletionKernels
public import PaperP1.Probability.PositionalKernelCoupling

/-! # Deleting an accidental background pair costs only its actual event mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalBackgroundDeletion

open PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositivePositionalConvolution
  PaperP1.PositionalPairDeletion PaperP1.PositionalDeletionKernels

variable {ι : Type*}

local instance backgroundDeletionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem identity_action (ν : Space ι) :
    PositionalMarkovKernel.action (fun v ↦ ofFinite (atom v))
      PositionalDeterministicMap.atom_isProbability ν = ν := by
  exact (PositionalCoefficientExpansion.hasSum_coeff_atoms ν).tsum_eq

theorem once_event_bound (E : Finset (Finset ι)) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) :
    ‖once E ν - ν‖ ≤ 2 * ∑' v, if (activeEdges E v).Nonempty then coeff v ν else 0 := by
  have hh := PositionalKernelCoupling.event_bound (onceKernel E) (fun v ↦ ofFinite (atom v))
    (onceKernel_isProbability E) PositionalDeterministicMap.atom_isProbability ν hν
    (fun v ↦ (activeEdges E v).Nonempty) (fun v hv ↦ Or.inr (by
      rw [onceKernel, ite_eq_right hv]))
  simp only [identity_action] at hh
  convert hh using 1
  · rfl
  · apply congrArg (fun r : ℝ ↦ 2 * r)
    apply tsum_congr
    intro v
    by_cases hv : (activeEdges E v).Nonempty
    · simp only [ite_eq_left hv]
    · simp only [ite_eq_right hv]

theorem isolated_event_bound (E : Finset (Finset ι)) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) :
    ‖isolated E ν - ν‖ ≤ 2 * ∑' v, if (activeEdges E v).Nonempty then coeff v ν else 0 := by
  have hh := PositionalKernelCoupling.event_bound
    (fun v ↦ ofFinite (atom (isolate E v))) (fun v ↦ ofFinite (atom v))
    (fun v ↦ PositionalDeterministicMap.atom_isProbability (isolate E v))
    PositionalDeterministicMap.atom_isProbability ν hν
    (fun v ↦ (activeEdges E v).Nonempty) (fun v hv ↦ Or.inr (by
      rw [isolate_eq_self_of_no_active E v (Finset.not_nonempty_iff_eq_empty.mp hv)]))
  simp only [identity_action] at hh
  convert hh using 1
  · rfl
  · apply congrArg (fun r : ℝ ↦ 2 * r)
    apply tsum_congr
    intro v
    by_cases hv : (activeEdges E v).Nonempty
    · simp only [ite_eq_left hv]
    · simp only [ite_eq_right hv]

end PaperP1.PositionalBackgroundDeletion
