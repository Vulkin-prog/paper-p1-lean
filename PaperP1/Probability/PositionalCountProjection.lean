module

public import PaperP1.Probability.PositionalCoefficientExpansion
public import PaperP1.Probability.PositionalPoissonJump
public import PaperP1.Probability.HermiteReference
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # The continuous projection from full fields to their total counts

The projection sums configurations of the same total size. It is a contraction
for the ordinary ℓ¹ norm and preserves convolution, including its completion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCountProjection

open Finset UniformSpace PaperP1.PositionalFiniteLaw

variable {ι Ω : Type*}

def totalCount : Configuration ι →+ ℕ :=
  Finsupp.liftAddHom (fun _ : ι ↦ AddMonoidHom.id ℕ)

@[simp] theorem totalCount_single (x : ι) (n : ℕ) :
    totalCount (Finsupp.single x n) = n := by
  simp [totalCount]

@[simp] theorem totalCount_direction (x : ι) : totalCount (direction x) = 1 :=
  totalCount_single x 1

theorem totalCount_configuration (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    totalCount (configuration G J ω) = ∑ x ∈ G, (J x ω).toNat := by
  simp [configuration]

def finiteMap : FieldLaw ι →+* Probability.SignedLaw ℝ :=
  AddMonoidAlgebra.mapDomainRingHom ℝ totalCount

def finiteLinear : FieldLaw ι →ₗ[ℝ] Probability.SignedLaw ℝ :=
  AddMonoidAlgebra.mapDomainLinearMap ℝ ℝ totalCount

theorem finiteLinear_eq (ν : FieldLaw ι) : finiteLinear ν = finiteMap ν := rfl

@[simp] theorem finiteLinear_single (v : Configuration ι) (r : ℝ) :
    finiteLinear (AddMonoidAlgebra.single v r) =
      AddMonoidAlgebra.single (totalCount v) r := by
  simp [finiteLinear]

theorem norm_finiteLinear_le (ν : FieldLaw ι) :
    ‖finiteLinear ν‖ ≤ ‖ν‖ := by
  classical
  have he : finiteLinear ν = ∑ v ∈ ν.coeff.support,
      AddMonoidAlgebra.single (totalCount v) (ν.coeff v) := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
    simp only [Finsupp.sum, map_sum, finiteLinear_single]
  rw [he]
  calc
    _ ≤ ∑ v ∈ ν.coeff.support,
        ‖(AddMonoidAlgebra.single (totalCount v) (ν.coeff v) : CompletedLaw.Finite)‖ :=
      norm_sum_le _ _
    _ = ‖ν‖ := by
      simp only [CompletedLaw.norm_finite, Probability.l1Norm_single,
        CompletedPositionalLaw.norm_finite, FiniteConvolutionAlgebra.l1Norm, Finsupp.sum]

def finiteContinuous : CompletedPositionalLaw.Finite ι →L[ℝ] CompletedLaw.Finite :=
  LinearMap.mkContinuous finiteLinear 1 (fun ν ↦ by
    simpa only [one_mul] using norm_finiteLinear_le ν)

def finiteProjection : CompletedPositionalLaw.Finite ι →L[ℝ] CompletedLaw.Space :=
  (Completion.toComplL : CompletedLaw.Finite →L[ℝ] CompletedLaw.Space).comp finiteContinuous

def projection : CompletedPositionalLaw.Space ι →L[ℝ] CompletedLaw.Space :=
  finiteProjection.fromCompletion

@[simp] theorem projection_ofFinite (ν : FieldLaw ι) :
    projection (CompletedPositionalLaw.ofFinite ν) = CompletedLaw.ofFinite (finiteMap ν) :=
  ContinuousLinearMap.fromCompletion_apply_coe finiteProjection ν

theorem norm_projection_le (ν : CompletedPositionalLaw.Space ι) :
    ‖projection ν‖ ≤ ‖ν‖ := by
  induction ν using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) continuous_norm
  | ih ν =>
    change ‖projection (CompletedPositionalLaw.ofFinite ν)‖ ≤
      ‖CompletedPositionalLaw.ofFinite ν‖
    rw [projection_ofFinite, CompletedLaw.norm_ofFinite, CompletedPositionalLaw.norm_ofFinite]
    exact norm_finiteLinear_le ν

@[simp] theorem projection_one : projection (1 : CompletedPositionalLaw.Space ι) = 1 := by
  rw [← map_one (CompletedPositionalLaw.ofFinite : FieldLaw ι →+* _),
    projection_ofFinite, map_one, map_one]

theorem projection_mul (ν κ : CompletedPositionalLaw.Space ι) :
    projection (ν * κ) = projection ν * projection κ := by
  induction ν, κ using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih ν κ =>
    change projection (CompletedPositionalLaw.ofFinite ν * CompletedPositionalLaw.ofFinite κ) =
      projection (CompletedPositionalLaw.ofFinite ν) * projection (CompletedPositionalLaw.ofFinite κ)
    rw [← map_mul, projection_ofFinite, projection_ofFinite, projection_ofFinite,
      map_mul, map_mul]

def projectionHom : CompletedPositionalLaw.Space ι →+* CompletedLaw.Space where
  toFun := projection
  map_zero' := map_zero projection
  map_add' := map_add projection
  map_one' := projection_one
  map_mul' := projection_mul

@[simp] theorem projection_atom (v : Configuration ι) :
    projection (CompletedPositionalLaw.ofFinite (FiniteConvolutionAlgebra.atom v)) =
      CompletedLaw.ofFinite (Probability.atom (totalCount v)) := by
  rw [projection_ofFinite]
  simp [finiteMap, FiniteConvolutionAlgebra.atom, Probability.atom]

@[simp] theorem projection_delta (x : ι) :
    projection (CompletedPositionalLaw.ofFinite (delta x)) = CompletedPoisson.delta := by
  simp only [delta, map_sub, projection_atom, totalCount_direction, map_one,
    projection_one, CompletedPoisson.delta, Probability.forwardDifference,
    Probability.atom_zero]

theorem projection_difference (I : Finset ι) :
    projection (CompletedPositionalLaw.ofFinite (difference I)) =
      CompletedPoisson.delta ^ I.card := by
  change projectionHom (CompletedPositionalLaw.ofFinite (difference I)) = _
  simp only [difference, map_prod]
  change (∏ x ∈ I, projection (CompletedPositionalLaw.ofFinite (delta x))) = _
  simp only [projection_delta, prod_const]

theorem projection_exp (ν : CompletedPositionalLaw.Space ι) :
    projection (NormedSpace.exp ν) = NormedSpace.exp (projection ν) :=
  NormedSpace.map_exp projectionHom projection.continuous ν

theorem hasSum_projection_coeff (ν : CompletedPositionalLaw.Space ι) (k : ℕ) :
    HasSum (fun v ↦ if totalCount v = k then CompletedPositionalLaw.coeff v ν else 0)
      (CompletedLaw.coeff k (projection ν)) := by
  classical
  have hh := ((PositionalCoefficientExpansion.hasSum_coeff_atoms ν).map
    projection projection.continuous).map (CompletedLaw.coeff k) (CompletedLaw.coeff k).continuous
  have he (v : Configuration ι) :
      CompletedLaw.coeff k (projection
        (CompletedPositionalLaw.coeff v ν •
          CompletedPositionalLaw.ofFinite (FiniteConvolutionAlgebra.atom v))) =
        if totalCount v = k then CompletedPositionalLaw.coeff v ν else 0 := by
    simp only [map_smul, projection_atom, CompletedLaw.coeff_ofFinite,
      Probability.atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> ring
  simpa only [Function.comp_def, he] using hh

theorem projection_coeff (ν : CompletedPositionalLaw.Space ι) (k : ℕ) :
    CompletedLaw.coeff k (projection ν) =
      PushforwardMass.map totalCount (fun v ↦ CompletedPositionalLaw.coeff v ν) k := by
  classical
  rw [← (hasSum_projection_coeff ν k).tsum_eq]
  unfold PushforwardMass.map
  convert (tsum_subtype ({v : Configuration ι | totalCount v = k})
    (fun v ↦ CompletedPositionalLaw.coeff v ν)).symm using 1
  apply tsum_congr
  intro v
  by_cases hv : totalCount v = k <;> simp [hv]

end PaperP1.PositionalCountProjection
