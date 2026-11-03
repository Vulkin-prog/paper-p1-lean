module

public import PaperP1.Probability.PositionalFiniteLaw
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Normed.Module.Completion

/-! # The ordinary ℓ¹ completion of full positional convolution laws -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedPositionalLaw

open Finset UniformSpace PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw

variable {ι : Type*}

abbrev Finite (ι : Type*) := FieldLaw ι

theorem abs_coeff_le (ν : Finite ι) (v : Configuration ι) : |ν.coeff v| ≤ l1Norm ν := by
  classical
  by_cases hv : v ∈ ν.coeff.support
  · exact single_le_sum (fun i _ ↦ abs_nonneg (ν.coeff i)) hv
  · rw [Finsupp.notMem_support_iff.mp hv, abs_zero]
    exact l1Norm_nonneg ν

theorem zero_of_l1Norm_eq_zero (ν : Finite ι) (hν : l1Norm ν = 0) : ν = 0 := by
  ext v
  have hh := abs_coeff_le ν v
  rw [hν] at hh
  exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))

def ringNorm (ι : Type*) : RingNorm (Finite ι) where
  toFun := l1Norm
  map_zero' := l1Norm_zero
  add_le' := l1Norm_add
  neg' := l1Norm_neg
  mul_le' := l1Norm_mul
  eq_zero_of_map_eq_zero' := zero_of_l1Norm_eq_zero

instance : NormedCommRing (Finite ι) where
  __ := (ringNorm ι).toNormedRing
  mul_comm := mul_comm

theorem norm_finite (ν : Finite ι) : ‖ν‖ = l1Norm ν := rfl

theorem finite_l1Norm_eq_tsum (ν : Finite ι) : l1Norm ν = ∑' v, |ν.coeff v| := by
  unfold l1Norm Finsupp.sum
  symm
  apply tsum_eq_sum
  intro v hv
  rw [Finsupp.notMem_support_iff.mp hv, abs_zero]

theorem finite_norm_smul (c : ℝ) (ν : Finite ι) : ‖c • ν‖ = ‖c‖ * ‖ν‖ := by
  change l1Norm (c • ν) = ‖c‖ * l1Norm ν
  rw [finite_l1Norm_eq_tsum, finite_l1Norm_eq_tsum]
  change (∑' v, |c * ν.coeff v|) = ‖c‖ * ∑' v, |ν.coeff v|
  simp only [abs_mul, tsum_mul_left, Real.norm_eq_abs]

instance : NormedAlgebra ℝ (Finite ι) where
  norm_smul_le c ν := (finite_norm_smul c ν).le

instance : NormOneClass (Finite ι) := ⟨l1Norm_one⟩

abbrev Space (ι : Type*) := Completion (Finite ι)

def ofFinite : Finite ι →+* Space ι :=
  (Completion.coeRingHom : Finite ι →+* Space ι).comp
    { toFun := fun ν ↦ ν
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

theorem norm_ofFinite (ν : Finite ι) : ‖ofFinite ν‖ = l1Norm ν := Completion.norm_coe ν

instance : NormOneClass (Space ι) where
  norm_one := by
    change ‖ofFinite (1 : Finite ι)‖ = 1
    rw [norm_ofFinite, l1Norm_one]

def finiteCoeff (v : Configuration ι) : Finite ι →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun ν ↦ ν.coeff v
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun ν ↦ by
      change |ν.coeff v| ≤ 1 * l1Norm ν
      simpa only [one_mul] using abs_coeff_le ν v)

def coeff (v : Configuration ι) : Space ι →L[ℝ] ℝ := (finiteCoeff v).fromCompletion

@[simp]
theorem coeff_ofFinite (ν : Finite ι) (v : Configuration ι) : coeff v (ofFinite ν) = ν.coeff v :=
  ContinuousLinearMap.fromCompletion_apply_coe (finiteCoeff v) ν

theorem finite_sum_abs_coeff_le (ν : Space ι) (s : Finset (Configuration ι)) :
    ∑ v ∈ s, |coeff v ν| ≤ ‖ν‖ := by
  induction ν using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) continuous_norm
  | ih ν =>
    change (∑ v ∈ s, |coeff v (ofFinite ν)|) ≤ ‖ofFinite ν‖
    simp only [coeff_ofFinite, norm_ofFinite]
    rw [finite_l1Norm_eq_tsum]
    exact Summable.sum_le_tsum s (fun _ _ ↦ abs_nonneg _)
      (summable_of_hasFiniteSupport ν.coeff.hasFiniteSupport).abs

theorem summable_abs_coeff (ν : Space ι) : Summable (fun v ↦ |coeff v ν|) :=
  summable_of_sum_le (fun _ ↦ abs_nonneg _) (finite_sum_abs_coeff_le ν)

theorem tsum_abs_coeff_le (ν : Space ι) : (∑' v, |coeff v ν|) ≤ ‖ν‖ :=
  Real.tsum_le_of_sum_le (fun _ ↦ abs_nonneg _) (finite_sum_abs_coeff_le ν)

theorem summable_coeff (ν : Space ι) : Summable (fun v ↦ coeff v ν) := (summable_abs_coeff ν).of_abs

theorem norm_delta_le (x : ι) : ‖ofFinite (delta x)‖ ≤ 2 := by
  rw [norm_ofFinite]
  exact delta_l1Norm x

end PaperP1.CompletedPositionalLaw
