module

public import PaperP1.Probability.CompletedPositionalLaw
public import PaperP1.Probability.PoissonSequence
public import PaperP1.Analysis.BanachExponentialRemainder
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # A Poisson arrival at an actual configuration, with literal coefficients

The jump configuration can be a single site or the endpoints of a pair.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonJump

open Finset PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw

variable {ι : Type*}

local instance positionalPoissonJumpDecidable (P : Prop) : Decidable P := Classical.propDecidable P

instance : NormedAlgebra ℚ (Space ι) := NormedAlgebra.restrictScalars ℚ ℝ (Space ι)

def jump (m : Configuration ι) (μ : ℝ) : Space ι :=
  NormedSpace.exp (μ • (ofFinite (atom m) - 1))

theorem atom_power (m : Configuration ι) (n : ℕ) : (atom m : FieldLaw ι) ^ n = atom (n • m) := by
  simp only [atom, AddMonoidAlgebra.single_pow, one_pow]

theorem coeff_atom_power (m v : Configuration ι) (n : ℕ) :
    coeff v ((ofFinite (atom m)) ^ n) = if n • m = v then 1 else 0 := by
  rw [← map_pow, atom_power, coeff_ofFinite]
  simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem coeff_exponential_atom (m v : Configuration ι) (μ : ℝ) :
    coeff v (NormedSpace.exp (μ • ofFinite (atom m))) =
      ∑' n : ℕ, if n • m = v then μ ^ n / (n.factorial : ℝ) else 0 := by
  have hh := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (μ • ofFinite (atom m))).map (coeff v) (coeff v).continuous
  have heq (n : ℕ) : coeff v (((n.factorial : ℝ)⁻¹) • (μ • ofFinite (atom m)) ^ n) =
      if n • m = v then μ ^ n / (n.factorial : ℝ) else 0 := by
    simp only [map_smul, smul_pow, coeff_atom_power, smul_eq_mul]
    split_ifs <;> ring
  dsimp only [Function.comp_def] at hh
  simp_rw [heq] at hh
  exact hh.tsum_eq.symm

theorem exponential_scalar (r : ℝ) :
    NormedSpace.exp (algebraMap ℝ (Space ι) r) = Real.exp r • (1 : Space ι) := by
  rw [← NormedSpace.map_exp (algebraMap ℝ (Space ι)) (continuous_algebraMap _ _) r,
    ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]

theorem factorization (m : Configuration ι) (μ : ℝ) :
    jump m μ = Real.exp (-μ) • NormedSpace.exp (μ • ofFinite (atom m)) := by
  have he : μ • (ofFinite (atom m) - 1) = algebraMap ℝ (Space ι) (-μ) + μ • ofFinite (atom m) := by
    rw [Algebra.algebraMap_eq_smul_one, neg_smul, smul_sub]
    abel
  rw [jump, he, NormedSpace.exp_add, exponential_scalar, smul_mul_assoc, one_mul]

theorem coeff_jump (m v : Configuration ι) (μ : ℝ) :
    coeff v (jump m μ) = ∑' n : ℕ, if n • m = v then PoissonSequence.mass μ n else 0 := by
  rw [factorization, map_smul, coeff_exponential_atom, smul_eq_mul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs <;> simp [PoissonSequence.mass, mul_div_assoc]

theorem coeff_jump_nonneg (m v : Configuration ι) (μ : ℝ) (hμ : 0 ≤ μ) :
    0 ≤ coeff v (jump m μ) := by
  rw [coeff_jump]
  apply tsum_nonneg
  intro n
  split_ifs
  · unfold PoissonSequence.mass
    positivity
  · exact le_rfl

theorem coeff_jump_fiber (m v : Configuration ι) (μ : ℝ) :
    coeff v (jump m μ) = ∑' n : {n : ℕ // n • m = v}, PoissonSequence.mass μ n.val := by
  rw [coeff_jump]
  convert (tsum_subtype ({n : ℕ | n • m = v}) (PoissonSequence.mass μ)).symm using 1
  apply tsum_congr
  intro n
  by_cases hn : n • m = v <;> simp [hn]

theorem hasSum_coeff_jump (m : Configuration ι) (μ : ℝ) (hμ : 0 ≤ μ) :
    HasSum (fun v ↦ coeff v (jump m μ)) 1 := by
  have hh := (PoissonSequence.hasSum_mass μ hμ).tsum_fiberwise (fun n : ℕ ↦ n • m)
  convert hh using 1
  funext v
  exact coeff_jump_fiber m v μ

theorem norm_jump_le_one (m : Configuration ι) (μ : ℝ) (hμ : 0 ≤ μ) : ‖jump m μ‖ ≤ 1 := by
  have hn : ‖μ • ofFinite (atom m)‖ = μ := by
    rw [norm_smul, norm_ofFinite, l1Norm_atom, mul_one, Real.norm_eq_abs, abs_of_nonneg hμ]
  rw [factorization, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-μ) * Real.exp ‖μ • ofFinite (atom m)‖ :=
      mul_le_mul_of_nonneg_left (BanachExponentialRemainder.norm_exp_le _) (Real.exp_nonneg _)
    _ = 1 := by rw [hn, ← Real.exp_add]; simp

end PaperP1.PositionalPoissonJump
