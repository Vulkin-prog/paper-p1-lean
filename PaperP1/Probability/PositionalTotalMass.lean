module

public import PaperP1.Probability.PositionalPoissonJump

/-! # Continuous total mass of completed positional laws -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalTotalMass

open Finset UniformSpace PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw

variable {ι : Type*}

def totalMass : Space ι →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun ν ↦ ∑' v, coeff v ν
      map_add' := fun ν κ ↦ by
        simp only [map_add]
        exact (summable_coeff ν).tsum_add (summable_coeff κ)
      map_smul' := fun r ν ↦ by
        simp only [map_smul, smul_eq_mul, tsum_mul_left, RingHom.id_apply] }
    1 (fun ν ↦ by
      rw [one_mul]
      exact (norm_tsum_le_tsum_norm (summable_coeff ν).norm).trans
        (by simpa only [Real.norm_eq_abs] using tsum_abs_coeff_le ν))

theorem totalMass_eq_tsum (ν : Space ι) : totalMass ν = ∑' v, coeff v ν := rfl

theorem totalMass_ofFinite (ν : FieldLaw ι) : totalMass (ofFinite ν) = mass ν := by
  rw [totalMass_eq_tsum]
  simp only [coeff_ofFinite]
  rw [mass_eq_sum_coeff]
  exact tsum_eq_sum fun v hv ↦ Finsupp.notMem_support_iff.mp hv

theorem totalMass_one : totalMass (1 : Space ι) = 1 := by
  rw [← map_one (ofFinite : FieldLaw ι →+* Space ι), totalMass_ofFinite, map_one]

theorem totalMass_mul (ν κ : Space ι) : totalMass (ν * κ) = totalMass ν * totalMass κ := by
  induction ν, κ using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih ν κ =>
    change totalMass (ofFinite ν * ofFinite κ) = totalMass (ofFinite ν) * totalMass (ofFinite κ)
    rw [← map_mul, totalMass_ofFinite, totalMass_ofFinite, totalMass_ofFinite, map_mul]

def totalMassHom : Space ι →+* ℝ where
  toFun := totalMass
  map_zero' := map_zero totalMass
  map_add' := map_add totalMass
  map_one' := totalMass_one
  map_mul' := totalMass_mul

theorem totalMass_jump (m : Configuration ι) (μ : ℝ) (hμ : 0 ≤ μ) :
    totalMass (PositionalPoissonJump.jump m μ) = 1 :=
  (PositionalPoissonJump.hasSum_coeff_jump m μ hμ).tsum_eq

theorem hasSum_coeff_of_totalMass_eq_one (ν : Space ι) (hν : totalMass ν = 1) :
    HasSum (fun v ↦ coeff v ν) 1 := by
  have hh := (summable_coeff ν).hasSum
  rwa [← totalMass_eq_tsum, hν] at hh

end PaperP1.PositionalTotalMass
