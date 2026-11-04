module

public import PaperP1.Probability.PositionalMarkovKernel

/-! # Two field kernels can differ only on a charged exceptional event -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalKernelCoupling

open PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositivePositionalConvolution PaperP1.PositionalMarkovKernel

variable {ι κ : Type*}

local instance kernelCouplingDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem event_bound (K K' : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (hK' : ∀ v, IsProbability (K' v))
    (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν) (B : Configuration ι → Prop)
    (hsame : ∀ v, ¬ B v → coeff v ν = 0 ∨ K v = K' v) :
    ‖action K hK ν - action K' hK' ν‖ ≤
      2 * ∑' v, if B v then coeff v ν else 0 := by
  have hsB : Summable (fun v ↦ if B v then coeff v ν else 0) :=
    Summable.of_nonneg_of_le (fun v ↦ by split_ifs; exact hν v; exact le_rfl)
      (fun v ↦ by split_ifs; exact le_rfl; exact hν v) (summable_coeff ν)
  have hd (v : Configuration ι) : ‖K v - K' v‖ ≤ 2 := by
    have hh := norm_sub_le (K v) (K' v)
    simpa only [norm_isProbability (hK v), norm_isProbability (hK' v), one_add_one_eq_two] using hh
  have hpoint (v : Configuration ι) : ‖coeff v ν • (K v - K' v)‖ ≤
      2 * (if B v then coeff v ν else 0) := by
    by_cases hv : B v
    · rw [ite_eq_left hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hν v)]
      nlinarith only [mul_le_mul_of_nonneg_left (hd v) (hν v)]
    · rw [ite_eq_right hv, mul_zero]
      rcases hsame v hv with hz | he
      · rw [hz, zero_smul, norm_zero]
      · rw [he, sub_self, smul_zero, norm_zero]
  have hsnorm : Summable (fun v ↦ ‖coeff v ν • (K v - K' v)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hpoint (hsB.mul_left 2)
  have he : action K hK ν - action K' hK' ν =
      ∑' v, coeff v ν • (K v - K' v) := by
    rw [action_eq_tsum, action_eq_tsum,
      ← (summable_atoms K hK ν).tsum_sub (summable_atoms K' hK' ν)]
    simp only [smul_sub]
  rw [he]
  calc
    _ ≤ ∑' v, ‖coeff v ν • (K v - K' v)‖ := norm_tsum_le_tsum_norm hsnorm
    _ ≤ ∑' v, 2 * (if B v then coeff v ν else 0) :=
      hsnorm.tsum_le_tsum hpoint (hsB.mul_left 2)
    _ = _ := tsum_mul_left

end PaperP1.PositionalKernelCoupling
