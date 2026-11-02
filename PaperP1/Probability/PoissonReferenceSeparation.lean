module

public import PaperP1.Probability.QuadraticPoisson
public import Mathlib.Tactic.Linarith

/-! # A quantitative lower bound for a change of mean in the quadratic reference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonReferenceSeparation

open Finset PaperP1.PoissonSequence

theorem ordered_exponential_difference {u v M : ℝ} (huv : u ≤ v) (hv : v ≤ M) :
    Real.exp (-M) * (v - u) ≤ Real.exp (-u) - Real.exp (-v) := by
  have ht := Real.add_one_le_exp (v - u)
  have hmul := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-v)).le
  have hidentity : Real.exp (-v) * Real.exp (v - u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hidentity] at hmul
  have hscale := mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith : -M ≤ -v)) (sub_nonneg.mpr huv)
  nlinarith only [hmul, hscale]

theorem exponential_difference {u v M : ℝ} (hu : u ≤ M) (hv : v ≤ M) :
    Real.exp (-M) * |u - v| ≤ |Real.exp (-u) - Real.exp (-v)| := by
  rcases le_total u v with huv | hvu
  · have h := ordered_exponential_difference huv hv
    rw [abs_of_nonpos (sub_nonpos.mpr huv), abs_of_nonneg
      (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith : -v ≤ -u)))]
    nlinarith only [h]
  · have h := ordered_exponential_difference hvu hu
    rw [abs_of_nonneg (sub_nonneg.mpr hvu), abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith : -u ≤ -v)))]
    nlinarith only [h]

theorem quadratic_mass_zero (μ α : ℝ) : quadraticMass μ α 0 = Real.exp (-μ) * (1 + α / 2) := by
  simp only [quadraticMass, secondDifference, shift_zero, mass, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one, mul_zero, sub_zero, zero_add]
  ring

theorem zero_mass_separation {μ ν M α : ℝ} (hμ : μ ≤ M) (hν : ν ≤ M) (hα : -1 ≤ α) :
    (Real.exp (-M) / 2) * |μ - ν| ≤ |quadraticMass μ α 0 - quadraticMass ν α 0| := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 + α / 2 := by linarith
  have hfactor : 0 ≤ 1 + α / 2 := by linarith
  rw [quadratic_mass_zero, quadratic_mass_zero, ← sub_mul, abs_mul, abs_of_nonneg hfactor]
  have hexp := exponential_difference hμ hν
  have h₁ := mul_le_mul_of_nonneg_right hexp (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h₂ := mul_le_mul_of_nonneg_left hhalf (abs_nonneg (Real.exp (-μ) - Real.exp (-ν)))
  nlinarith only [h₁, h₂]

theorem actual_reference_separation {μ ν M α : ℝ} (hμ₀ : 0 ≤ μ) (hν₀ : 0 ≤ ν)
    (hμ : μ ≤ M) (hν : ν ≤ M) (hα : -1 ≤ α) :
    (Real.exp (-M) / 2) * |μ - ν| ≤
      ∑' k : ℕ, |(PaperP1.QuadraticPoisson.reference μ α - PaperP1.QuadraticPoisson.reference ν α) {k}| := by
  have hs := ((hasSum_quadraticMass μ α hμ₀).summable.sub (hasSum_quadraticMass ν α hν₀).summable).abs
  have hzero : |quadraticMass μ α 0 - quadraticMass ν α 0| ≤
      ∑' k, |quadraticMass μ α k - quadraticMass ν α k| := by
    simpa only [sum_singleton] using hs.sum_le_tsum {0} (fun _ _ ↦ abs_nonneg _)
  have heval (k : ℕ) :
      (PaperP1.QuadraticPoisson.reference μ α - PaperP1.QuadraticPoisson.reference ν α) {k} =
        quadraticMass μ α k - quadraticMass ν α k := by
    rw [_root_.sub_apply, PaperP1.QuadraticPoisson.reference, PaperP1.QuadraticPoisson.reference,
      PaperP1.AtomicSignedLaw.ofSequence_singleton (hasSum_quadraticMass μ α hμ₀).summable,
      PaperP1.AtomicSignedLaw.ofSequence_singleton (hasSum_quadraticMass ν α hν₀).summable]
  simp_rw [heval]
  exact (zero_mass_separation hμ hν hα).trans hzero

end PaperP1.PoissonReferenceSeparation
