module

public import PaperP1.Probability.PositionalGroundSupport
public import PaperP1.Probability.PositionalDeletionKernels

/-! # Deletion kernels preserve the literal finite ground, even for signed inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletionSupport

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalGroundSupport PaperP1.PositionalPairDeletion
  PaperP1.PositionalDeletionKernels

variable {ι α : Type*}

theorem onGround_mono (G : Finset ι) {u v : Configuration ι}
    (hv : OnGround G v) (huv : ∀ x, u x ≤ v x) : OnGround G u := by
  intro x hx
  exact Nat.eq_zero_of_le_zero (by simpa only [hv x hx] using huv x)

theorem supported_atom (G : Finset ι) (v : Configuration ι) (hv : OnGround G v) :
    Supported G (ofFinite (FiniteConvolutionAlgebra.atom v)) := by
  classical
  intro w hw
  have hne : v ≠ w := fun he ↦ hw (he ▸ hv)
  simp only [coeff_ofFinite, FiniteConvolutionAlgebra.atom,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]

theorem supported_action (G : Finset ι) (ν : Space ι) (hν : Supported G ν)
    (K : Configuration ι → Space ι) (hK : ∀ v, PositivePositionalConvolution.IsProbability (K v))
    (hground : ∀ v, OnGround G v → Supported G (K v)) :
    Supported G (PositionalMarkovKernel.action K hK ν) := by
  intro w hw
  rw [PositionalMarkovKernel.coeff_action]
  refine (tsum_congr (g := fun _ : Configuration ι ↦ (0 : ℝ)) (fun v ↦ ?_)).trans tsum_zero
  by_cases hv : OnGround G v
  · rw [hground v hv w hw, mul_zero]
  · rw [hν v hv, zero_mul]

theorem supported_average (G : Finset ι) (S : Finset α) (f : α → Configuration ι)
    (hf : ∀ a ∈ S, OnGround G (f a)) : Supported G (PositionalUniformAtoms.average S f) := by
  intro w hw
  rw [PositionalUniformAtoms.average, map_smul, map_sum, smul_eq_mul]
  have hz : (∑ a ∈ S, coeff w (ofFinite (FiniteConvolutionAlgebra.atom (f a)))) = 0 :=
    sum_eq_zero (fun a ha ↦ supported_atom G (f a) (hf a ha) w hw)
  rw [hz, mul_zero]

theorem supported_onceKernel (G : Finset ι) (E : Finset (Finset ι))
    (v : Configuration ι) (hv : OnGround G v) : Supported G (onceKernel E v) := by
  classical
  by_cases hne : (activeEdges E v).Nonempty
  · rw [onceKernel, ite_eq_left hne]
    exact supported_average G _ _ (fun e _he ↦ onGround_mono G hv (deleteEdge_le e v))
  · rw [onceKernel, ite_eq_right hne]
    exact supported_atom G v hv

theorem supported_once (G : Finset ι) (E : Finset (Finset ι))
    (ν : Space ι) (hν : Supported G ν) : Supported G (once E ν) :=
  supported_action G ν hν _ _ (supported_onceKernel G E)

theorem supported_isolated (G : Finset ι) (E : Finset (Finset ι))
    (ν : Space ι) (hν : Supported G ν) : Supported G (isolated E ν) :=
  supported_action G ν hν _ (fun v ↦ PositionalDeterministicMap.atom_isProbability (isolate E v)) (fun v hv ↦
    supported_atom G (isolate E v) (onGround_mono G hv (isolate_le E v)))

end PaperP1.PositionalDeletionSupport
