module

public import PaperP1.Model.ColoredPrimeSamples
public import PaperP1.Probability.UniformFubini
public import PaperP1.Affine.NominalAffineMass
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Actual replica products, their colored joint event, and exact affine mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredReplicaMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples
  PaperP1.UniformFubini

local instance coloredReplicaMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance coloredReplicaMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def blockProbability {ι κ : Type*} {M : ℕ} (Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) (k : κ) (σ : SampleSpace M) : ℝ :=
  average (fun τ : SampleSpace M ↦
    if ∀ i, color i = k → startSystem M (x i) L (glue Y σ τ) = b i then 1 else 0)

def jointProbability {ι κ : Type*} [Fintype κ] (M Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) : ℝ :=
  average (fun ω : Sample κ M ↦ if ∀ i, start M Y (x i) L (color i) ω = b i then 1 else 0)

theorem replica_identity {ι κ : Type*} [Fintype κ] (M Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) :
    average (fun σ : SampleSpace M ↦ ∏ k, blockProbability Y L x color b k σ) =
      jointProbability M Y L x color b := by
  classical
  unfold jointProbability
  rw [UniformFubini.product]
  apply UniformFubini.congr
  intro σ
  unfold blockProbability
  rw [← UniformFubini.independent_product]
  apply UniformFubini.congr
  intro τ
  rw [Fintype.prod_boole]
  have hevent : (∀ k, ∀ i, color i = k → startSystem M (x i) L (glue Y σ (τ k)) = b i) ↔
      ∀ i, start M Y (x i) L (color i) (σ, τ) = b i := by
    constructor
    · intro h i
      exact h (color i) i rfl
    · intro h k i hi
      subst k
      exact h i
  simp only [hevent]

def jointSystem {ι κ : Type*} (M Y L : ℕ) (x : ι → ℕ) (color : ι → κ) :
    Sample κ M →ₗ[F₂] (ι × Fin L → F₂) :=
  LinearMap.pi (fun p ↦ (startRow M (x p.1) L p.2).comp (select M Y (color p.1)))

def jointRhs {ι : Type*} {L : ℕ} (b : ι → Fin L → F₂) : ι × Fin L → F₂ :=
  fun p ↦ b p.1 p.2

theorem joint_system_event {ι κ : Type*} (M Y L : ℕ) (x : ι → ℕ) (color : ι → κ)
    (b : ι → Fin L → F₂) (ω : Sample κ M) :
    jointSystem M Y L x color ω = jointRhs b ↔
      ∀ i, start M Y (x i) L (color i) ω = b i := by
  constructor
  · intro h i
    funext j
    exact congrFun h (i, j)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

theorem joint_eq_affine_mass {ι κ : Type*} [Fintype κ] (M Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) :
    jointProbability M Y L x color b = uniformSolutionMass (jointSystem M Y L x color) (jointRhs b) := by
  unfold jointProbability uniformSolutionMass
  apply UniformFubini.congr
  intro ω
  rw [joint_system_event]

theorem exact_nominal_formula {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M Y L : ℕ) (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂) :
    average (fun σ : SampleSpace M ↦ ∏ k, blockProbability Y L x color b k σ) =
      (if Compatible (jointSystem M Y L x color) (jointRhs b) then (1 : ℝ) else 0) *
      (2 ^ Module.finrank F₂ (LinearMap.ker (relationMap (jointSystem M Y L x color))) : ℝ) /
      (2 ^ (Fintype.card ι * L) : ℝ) := by
  classical
  rw [replica_identity, joint_eq_affine_mass, NominalAffineMass.exact_formula]
  simp only [Fintype.card_prod, Fintype.card_fin]

end PaperP1.ColoredReplicaMass
