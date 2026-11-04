module

public import PaperP1.Probability.PositionalCompoundPoisson
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Positional laws remain on their stated finite ground

Convolution and single/pair Poisson arrivals cannot introduce an outside site.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalGroundSupport

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCoefficientExpansion
  PaperP1.PositivePositionalConvolution

variable {ι Ω : Type*}

def OnGround (G : Finset ι) (v : Configuration ι) : Prop := ∀ x ∉ G, v x = 0

def Supported (G : Finset ι) (ν : Space ι) : Prop :=
  ∀ v, ¬ OnGround G v → coeff v ν = 0

theorem onGround_zero (G : Finset ι) : OnGround G 0 := by intro x _; rfl

theorem onGround_add (G : Finset ι) {u v : Configuration ι}
    (hu : OnGround G u) (hv : OnGround G v) : OnGround G (u + v) := by
  intro x hx
  simp only [Finsupp.add_apply, hu x hx, hv x hx, add_zero]

theorem onGround_nsmul (G : Finset ι) {v : Configuration ι} (hv : OnGround G v) (n : ℕ) :
    OnGround G (n • v) := by
  intro x hx
  simp only [Finsupp.smul_apply, hv x hx, smul_zero]

theorem onGround_direction (G : Finset ι) {x : ι} (hx : x ∈ G) : OnGround G (direction x) := by
  classical
  intro y hy
  have hxy : x ≠ y := by intro he; exact hy (he ▸ hx)
  simp [direction, hxy]

theorem onGround_sum_directions (G e : Finset ι) (he : e ⊆ G) :
    OnGround G (∑ x ∈ e, direction x) := by
  classical
  intro y hy
  rw [Finset.sum_apply']
  exact sum_eq_zero fun x hx ↦ onGround_direction G (he hx) y hy

theorem onGround_configuration (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    OnGround G (configuration G J ω) := by
  classical
  intro y hy
  unfold configuration
  rw [Finset.sum_apply']
  apply sum_eq_zero
  intro x hx
  have hxy : x ≠ y := by intro he; exact hy (he ▸ hx)
  simp [hxy]

theorem supported_law [Fintype Ω] (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    Supported G (ofFinite (law G w J)) := by
  classical
  intro v hv
  rw [coeff_ofFinite, law_coeff]
  apply sum_eq_zero
  intro ω _
  have hne : configuration G J ω ≠ v := fun he ↦ hv (he ▸ onGround_configuration G J ω)
  simp only [hne, ite_false]

theorem supported_one (G : Finset ι) : Supported G (1 : Space ι) := by
  classical
  intro v hv
  have hne : (0 : Configuration ι) ≠ v := fun he ↦ hv (he ▸ onGround_zero G)
  rw [← map_one (ofFinite : FieldLaw ι →+* Space ι), coeff_ofFinite]
  simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    hne, ite_false]

theorem supported_atom_mul (G : Finset ι) (u : Configuration ι) (hu : OnGround G u)
    (κ : Space ι) (hκ : Supported G κ) : Supported G (ofFinite (atom u) * κ) := by
  classical
  intro w hw
  have hh := (HasSum.mul_left (ofFinite (atom u)) (hasSum_coeff_atoms κ)).map (coeff w) (coeff w).continuous
  rw [← hh.tsum_eq]
  refine (tsum_congr (g := fun _ : Configuration ι ↦ (0 : ℝ)) (fun v ↦ ?_)).trans tsum_zero
  dsimp only [Function.comp_def]
  rw [mul_smul_comm, map_smul, ← map_mul, atom_mul, coeff_ofFinite]
  simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
  by_cases hv : OnGround G v
  · have hne : u + v ≠ w := fun he ↦ hw (he ▸ onGround_add G hu hv)
    simp only [hne, ite_false, mul_zero]
  · rw [hκ v hv, zero_mul]

theorem supported_mul (G : Finset ι) (ν κ : Space ι)
    (hν : Supported G ν) (hκ : Supported G κ) : Supported G (ν * κ) := by
  intro w hw
  have hh := (HasSum.mul_right κ (hasSum_coeff_atoms ν)).map (coeff w) (coeff w).continuous
  rw [← hh.tsum_eq]
  refine (tsum_congr (g := fun _ : Configuration ι ↦ (0 : ℝ)) (fun u ↦ ?_)).trans tsum_zero
  dsimp only [Function.comp_def]
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  by_cases hu : OnGround G u
  · rw [supported_atom_mul G u hu κ hκ w hw, mul_zero]
  · rw [hν u hu, zero_mul]

theorem supported_prod {α : Type*} (G : Finset ι) (S : Finset α) (f : α → Space ι)
    (hf : ∀ a ∈ S, Supported G (f a)) : Supported G (∏ a ∈ S, f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using supported_one G
  | @insert a S ha ih =>
    rw [prod_insert ha]
    exact supported_mul G _ _ (hf a (mem_insert_self _ _))
      (ih (fun b hb ↦ hf b (mem_insert_of_mem hb)))

theorem supported_jump (G : Finset ι) (m : Configuration ι) (hm : OnGround G m) (μ : ℝ) :
    Supported G (PositionalPoissonJump.jump m μ) := by
  classical
  intro v hv
  rw [PositionalPoissonJump.coeff_jump]
  refine (tsum_congr (g := fun _ : ℕ ↦ (0 : ℝ)) (fun n ↦ ?_)).trans tsum_zero
  have hne : n • m ≠ v := fun he ↦ hv (he ▸ onGround_nsmul G hm n)
  simp only [hne, ite_false]

theorem supported_target (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ) (hE : ∀ e ∈ E, e ⊆ G) :
    Supported G (PositionalCompoundPoisson.target G E p q) :=
  supported_mul G _ _
    (supported_prod G G _ (fun _x hx ↦ supported_jump G _ (onGround_direction G hx) _))
    (supported_prod G E _ (fun e he ↦ supported_jump G _ (onGround_sum_directions G e (hE e he)) _))

end PaperP1.PositionalGroundSupport
