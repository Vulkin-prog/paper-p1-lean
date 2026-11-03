module

public import PaperP1.Probability.PositionalCoefficientExpansion
public import PaperP1.Probability.PositionalTotalMass

/-! # Convolution preserves actual positional probability coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositivePositionalConvolution

open Finset PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCoefficientExpansion PaperP1.PositionalTotalMass

variable {ι : Type*}

theorem atom_mul (u v : Configuration ι) : (atom u : FieldLaw ι) * atom v = atom (u + v) := by
  simp [atom]

theorem coeff_atom_mul_nonneg (u w : Configuration ι) (κ : Space ι)
    (hκ : ∀ v, 0 ≤ coeff v κ) : 0 ≤ coeff w (ofFinite (atom u) * κ) := by
  have hh := (HasSum.mul_left (ofFinite (atom u)) (hasSum_coeff_atoms κ)).map (coeff w) (coeff w).continuous
  rw [← hh.tsum_eq]
  apply tsum_nonneg
  intro v
  dsimp only [Function.comp_def]
  rw [mul_smul_comm, map_smul, ← map_mul, atom_mul, coeff_ofFinite]
  have hv := hκ v
  classical
  simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> positivity

theorem coeff_mul_nonneg (ν κ : Space ι) (hν : ∀ v, 0 ≤ coeff v ν) (hκ : ∀ v, 0 ≤ coeff v κ)
    (w : Configuration ι) : 0 ≤ coeff w (ν * κ) := by
  have hh := (HasSum.mul_right κ (hasSum_coeff_atoms ν)).map (coeff w) (coeff w).continuous
  rw [← hh.tsum_eq]
  apply tsum_nonneg
  intro u
  dsimp only [Function.comp_def]
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  exact mul_nonneg (hν u) (coeff_atom_mul_nonneg u w κ hκ)

theorem coeff_one_nonneg (v : Configuration ι) : 0 ≤ coeff v (1 : Space ι) := by
  rw [← map_one (ofFinite : FieldLaw ι →+* Space ι), coeff_ofFinite]
  classical
  simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> norm_num

theorem coeff_prod_nonneg {α : Type*} (S : Finset α) (f : α → Space ι)
    (hf : ∀ a ∈ S, ∀ v, 0 ≤ coeff v (f a)) (v : Configuration ι) :
    0 ≤ coeff v (∏ a ∈ S, f a) := by
  classical
  revert v
  induction S using Finset.induction_on with
  | empty =>
    intro v
    simpa only [prod_empty] using coeff_one_nonneg v
  | @insert a S ha ih =>
    intro v
    rw [prod_insert ha]
    exact coeff_mul_nonneg _ _ (hf a (mem_insert_self _ _))
      (fun w ↦ ih (fun b hb ↦ hf b (mem_insert_of_mem hb)) w) v

def IsProbability (ν : Space ι) : Prop := (∀ v, 0 ≤ coeff v ν) ∧ totalMass ν = 1

theorem jump_isProbability (m : Configuration ι) (μ : ℝ) (hμ : 0 ≤ μ) :
    IsProbability (PositionalPoissonJump.jump m μ) :=
  ⟨fun v ↦ PositionalPoissonJump.coeff_jump_nonneg m v μ hμ, totalMass_jump m μ hμ⟩

theorem mul_isProbability {ν κ : Space ι} (hν : IsProbability ν) (hκ : IsProbability κ) :
    IsProbability (ν * κ) := by
  refine ⟨coeff_mul_nonneg ν κ hν.1 hκ.1, ?_⟩
  rw [totalMass_mul, hν.2, hκ.2, one_mul]

theorem prod_isProbability {α : Type*} (S : Finset α) (f : α → Space ι)
    (hf : ∀ a ∈ S, IsProbability (f a)) : IsProbability (∏ a ∈ S, f a) := by
  refine ⟨fun v ↦ coeff_prod_nonneg S f (fun a ha ↦ (hf a ha).1) v, ?_⟩
  change totalMassHom (∏ a ∈ S, f a) = 1
  rw [map_prod]
  exact prod_eq_one fun a ha ↦ (hf a ha).2

theorem norm_isProbability {ν : Space ι} (hν : IsProbability ν) : ‖ν‖ = 1 := by
  rw [norm_eq_tsum_abs_coeff]
  simp_rw [abs_of_nonneg (hν.1 _)]
  exact hν.2

end PaperP1.PositivePositionalConvolution
