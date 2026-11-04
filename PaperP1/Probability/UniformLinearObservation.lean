module

public import PaperP1.Affine.UniformPrecomposition
public import PaperP1.Probability.UniformFubini

/-! # Surjective finite linear observations have the full uniform law

The conclusion concerns every real observable, not just affine event masses.
All normalizations are the original P1 finite probability weights.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformLinearObservation

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.UniformFubini PaperP1.Affine

local instance uniformLinearObservationDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

theorem from_atoms {Ω W : Type*} [Fintype Ω] [Fintype W] [Nonempty W] [DecidableEq W]
    (P : FiniteProbability Ω) (Z : Ω → W)
    (hZ : ∀ b : W, finiteExpectation P.weight (fun ω ↦ if Z ω = b then (1 : ℝ) else 0) =
      (Fintype.card W : ℝ)⁻¹) (g : W → ℝ) :
    finiteExpectation P.weight (fun ω ↦ g (Z ω)) = average g := by
  have hp (ω : Ω) : g (Z ω) = ∑ b : W, if Z ω = b then g b else 0 := by
    simp [eq_comm]
  rw [show (fun ω ↦ g (Z ω)) =
    (fun ω ↦ ∑ b : W, if Z ω = b then g b else 0) from funext hp, finiteExpectation_sum]
  have ht (b : W) : finiteExpectation P.weight (fun ω ↦ if Z ω = b then g b else 0) =
      g b * (Fintype.card W : ℝ)⁻¹ := by
    have he : (fun ω ↦ if Z ω = b then g b else 0) =
        (fun ω ↦ g b * (if Z ω = b then (1 : ℝ) else 0)) := by
      funext ω
      by_cases h : Z ω = b <;> simp only [h, ite_true, ite_false, mul_one, mul_zero]
    rw [he, finiteExpectation_const_mul, hZ]
  simp_rw [ht]
  rw [average, uniformFiniteExpectation_eq, div_eq_mul_inv, sum_mul]

theorem id_mass {W : Type*} [AddCommGroup W] [Module 𝔽₂ W] [Fintype W] (b : W) :
    uniformSolutionMass (LinearMap.id : W →ₗ[𝔽₂] W) b = (Fintype.card W : ℝ)⁻¹ := by
  rw [uniformSolutionMass, uniformFiniteExpectation_eq]
  simp

theorem linear {V W : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
    [AddCommGroup W] [Module 𝔽₂ W] [Fintype W] [DecidableEq W]
    (f : V →ₗ[𝔽₂] W) (hf : Function.Surjective f) (g : W → ℝ) :
    average (fun v ↦ g (f v)) = average g := by
  apply from_atoms (uniformFiniteProbability V) f _ g
  intro b
  have h := UniformPrecomposition.mass_eq f hf (LinearMap.id : W →ₗ[𝔽₂] W) b
  rw [id_mass] at h
  have he : finiteExpectation (uniformFiniteProbability V).weight
      (fun v ↦ if f v = b then (1 : ℝ) else 0) =
      uniformSolutionMass ((LinearMap.id : W →ₗ[𝔽₂] W).comp f) b := by
    unfold uniformSolutionMass
    apply congrArg (finiteExpectation (uniformFiniteProbability V).weight)
    funext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    by_cases hh : f v = b <;> simp only [hh, ite_true, ite_false]
  exact he.trans h

end PaperP1.UniformLinearObservation
