module

public import PaperP1.Probability.PositionalAdditivePushforward
public import PaperP1.Probability.PositionalCountProjection
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Every additive natural-valued field observable has its exact scalar law

This includes a coordinate, a subset count and any fixed natural site weights.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalScalarProjection

open Finset PaperP1.PositionalFiniteLaw

variable {ι : Type*}

local instance scalarProjectionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def encode (φ : Configuration ι →+ ℕ) : Configuration ι →+ Configuration Unit :=
  (Finsupp.singleAddHom ()).comp φ

def projection (φ : Configuration ι →+ ℕ) : CompletedPositionalLaw.Space ι →L[ℝ] CompletedLaw.Space :=
  PositionalCountProjection.projection.comp (PositionalDeterministicMap.push (encode φ))

def projectionHom (φ : Configuration ι →+ ℕ) :
    CompletedPositionalLaw.Space ι →+* CompletedLaw.Space :=
  PositionalCountProjection.projectionHom.comp (PositionalAdditivePushforward.pushHom (encode φ))

theorem projectionHom_apply (φ : Configuration ι →+ ℕ) (ν : CompletedPositionalLaw.Space ι) :
    projectionHom φ ν = projection φ ν := rfl

theorem norm_projection_le (φ : Configuration ι →+ ℕ) (ν : CompletedPositionalLaw.Space ι) :
    ‖projection φ ν‖ ≤ ‖ν‖ := by
  have hh := PositionalDeterministicMap.contraction (encode φ) ν 0
  simp only [map_zero, sub_zero] at hh
  exact (PositionalCountProjection.norm_projection_le _).trans hh

theorem projection_atom (φ : Configuration ι →+ ℕ) (v : Configuration ι) :
    projection φ (CompletedPositionalLaw.ofFinite (FiniteConvolutionAlgebra.atom v)) =
      CompletedLaw.ofFinite (Probability.atom (φ v)) := by
  rw [projection, ContinuousLinearMap.comp_apply, PositionalDeterministicMap.push_atom,
    PositionalCountProjection.projection_atom]
  simp only [encode, AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply,
    PositionalCountProjection.totalCount_single]

theorem projection_exp (φ : Configuration ι →+ ℕ) (ν : CompletedPositionalLaw.Space ι) :
    projection φ (NormedSpace.exp ν) = NormedSpace.exp (projection φ ν) :=
  NormedSpace.map_exp (projectionHom φ) (projection φ).continuous ν

theorem projection_delta (φ : Configuration ι →+ ℕ) (x : ι) :
    projection φ (CompletedPositionalLaw.ofFinite (delta x)) =
      CompletedLaw.ofFinite (Probability.atom (φ (direction x))) - 1 := by
  rw [delta, map_sub, map_one, map_sub, projection_atom]
  exact congrArg (fun z ↦ CompletedLaw.ofFinite (Probability.atom (φ (direction x))) - z)
    (map_one (projectionHom φ))

theorem hasSum_projection_coeff (φ : Configuration ι →+ ℕ)
    (ν : CompletedPositionalLaw.Space ι) (k : ℕ) :
    HasSum (fun v ↦ if φ v = k then CompletedPositionalLaw.coeff v ν else 0)
      (CompletedLaw.coeff k (projection φ ν)) := by
  have hh := ((PositionalCoefficientExpansion.hasSum_coeff_atoms ν).map
    (projection φ) (projection φ).continuous).map (CompletedLaw.coeff k) (CompletedLaw.coeff k).continuous
  have he (v : Configuration ι) :
      CompletedLaw.coeff k (projection φ
        (CompletedPositionalLaw.coeff v ν •
          CompletedPositionalLaw.ofFinite (FiniteConvolutionAlgebra.atom v))) =
        if φ v = k then CompletedPositionalLaw.coeff v ν else 0 := by
    simp only [map_smul, projection_atom, CompletedLaw.coeff_ofFinite,
      Probability.atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> ring
  simpa only [Function.comp_def, he] using hh

theorem projection_coeff (φ : Configuration ι →+ ℕ)
    (ν : CompletedPositionalLaw.Space ι) (k : ℕ) :
    CompletedLaw.coeff k (projection φ ν) =
      PushforwardMass.map φ (fun v ↦ CompletedPositionalLaw.coeff v ν) k := by
  rw [← (hasSum_projection_coeff φ ν k).tsum_eq]
  unfold PushforwardMass.map
  convert (tsum_subtype ({v : Configuration ι | φ v = k})
    (fun v ↦ CompletedPositionalLaw.coeff v ν)).symm using 1
  apply tsum_congr
  intro v
  by_cases hv : φ v = k <;> simp [hv]

theorem summable_test (φ : Configuration ι →+ ℕ) (ν : CompletedPositionalLaw.Space ι)
    (hν : ∀ v, 0 ≤ CompletedPositionalLaw.coeff v ν) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hs : Summable (fun k ↦ CompletedLaw.coeff k (projection φ ν) * f k)) :
    Summable (fun v ↦ CompletedPositionalLaw.coeff v ν * f (φ v)) := by
  have hpart : ∀ v : Configuration ι, ∃! k : ℕ, v ∈ {w | φ w = k} := by
    intro v
    exact ⟨φ v, rfl, fun k hk ↦ hk.symm⟩
  apply (summable_partition (fun v ↦ mul_nonneg (hν v) (hf _)) hpart).mpr
  constructor
  · intro k
    have hh := ((CompletedPositionalLaw.summable_coeff ν).subtype
      (fun v ↦ φ v = k)).mul_right (f k)
    apply hh.congr
    intro v
    change CompletedPositionalLaw.coeff v.val ν * f k =
      CompletedPositionalLaw.coeff v.val ν * f (φ v.val)
    rw [v.property]
  · convert hs using 1
    funext k
    rw [projection_coeff]
    exact PushforwardMass.map_mul φ (fun v ↦ CompletedPositionalLaw.coeff v ν) f k

theorem test_eq (φ : Configuration ι →+ ℕ) (ν : CompletedPositionalLaw.Space ι)
    (hν : ∀ v, 0 ≤ CompletedPositionalLaw.coeff v ν) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hs : Summable (fun k ↦ CompletedLaw.coeff k (projection φ ν) * f k)) :
    (∑' v, CompletedPositionalLaw.coeff v ν * f (φ v)) =
      ∑' k, CompletedLaw.coeff k (projection φ ν) * f k := by
  simp only [projection_coeff]
  exact (PushforwardMass.test_map φ (fun v ↦ CompletedPositionalLaw.coeff v ν) f
    (summable_test φ ν hν f hf hs)).symm

end PaperP1.PositionalScalarProjection
