module

public import PaperP1.Analysis.MahlerCoefficientBounds

/-! # Passing a finite polynomial evaluation bound to coefficient energy

Only continuous polynomial functions are averaged. The pointwise premise
will be discharged by the specialization bound, not assumed as a factor-height
estimate. Parseval and finite linearity preserve the exact constant.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialParsevalBounds

open Polynomial Finset MahlerCoefficientBounds

theorem circleIntegrable_sq_norm_eval (p : ℂ[X]) :
    CircleIntegrable (fun z ↦ ‖p.eval z‖ ^ 2) 0 1 := by
  have hc : Continuous (fun z : ℂ ↦ ‖p.eval z‖ ^ 2) := by fun_prop
  exact hc.continuousOn.circleIntegrable'

theorem coefficient_energy_le_of_pointwise_bound {ι : Type*}
    (T : ℂ[X]) (s : Finset ι) (P : ι → ℂ[X]) (C : ℝ)
    (hbound : ∀ z : ℂ, ‖T.eval z‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) :
    coefficientEnergy T ≤ C ^ 2 * ∑ i ∈ s, coefficientEnergy (P i) := by
  have hT := circleIntegrable_sq_norm_eval T
  have hP (i : ι) := circleIntegrable_sq_norm_eval (P i)
  have hsum : CircleIntegrable (fun z : ℂ ↦ C ^ 2 * ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) 0 1 := by
    have hc : Continuous (fun z : ℂ ↦ C ^ 2 * ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) := by fun_prop
    exact hc.continuousOn.circleIntegrable'
  have hlinear : Real.circleAverage (fun z : ℂ ↦ C ^ 2 * ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) 0 1 =
      C ^ 2 * ∑ i ∈ s, coefficientEnergy (P i) := by
    calc
      _ = C ^ 2 * Real.circleAverage (fun z : ℂ ↦ ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) 0 1 := by
        simpa only [smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := C ^ 2)
            (f := fun z : ℂ ↦ ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) (c := 0) (R := 1))
      _ = _ := by
        rw [Real.circleAverage_fun_sum (fun i _ ↦ hP i)]
        congr 1
        apply sum_congr rfl
        intro i _
        exact (P i).sum_sq_norm_coeff_eq_circleAverage.symm
  calc
    _ = Real.circleAverage (fun z : ℂ ↦ ‖T.eval z‖ ^ 2) 0 1 := T.sum_sq_norm_coeff_eq_circleAverage
    _ ≤ Real.circleAverage (fun z : ℂ ↦ C ^ 2 * ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) 0 1 :=
      Real.circleAverage_mono hT hsum (fun z _ ↦ hbound z)
    _ = _ := hlinear

theorem l2_le_of_pointwise_bound {ι : Type*}
    (T : ℂ[X]) (s : Finset ι) (P : ι → ℂ[X]) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖T.eval z‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ s, ‖(P i).eval z‖ ^ 2) :
    l2CoefficientNorm T ≤ C * Real.sqrt (∑ i ∈ s, coefficientEnergy (P i)) := by
  have henergy := coefficient_energy_le_of_pointwise_bound T s P C hbound
  have hsum : 0 ≤ ∑ i ∈ s, coefficientEnergy (P i) :=
    sum_nonneg fun i _ ↦ coefficientEnergy_nonneg (P i)
  apply (sq_le_sq₀ (l2CoefficientNorm_nonneg T) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [l2CoefficientNorm_sq, mul_pow, Real.sq_sqrt hsum]
  exact henergy

end PaperP1.PolynomialParsevalBounds
