module

public import PaperP1.Probability.CompletedPoisson
public import PaperP1.Probability.QuadraticPoisson

/-! # Actual shifts and quadratic Poisson references in the completed algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedLawShift

open PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson UniformSpace
  PaperP1.PoissonSequence

theorem coeff_shift (ν : Space) (k : ℕ) :
    coeff k (ofFinite (atom 1) * ν) = shift (fun j ↦ coeff j ν) k := by
  cases k with
  | zero =>
    induction ν using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_const
    | ih ν =>
      change coeff 0 (ofFinite (atom 1) * ofFinite ν) = 0
      rw [← map_mul, coeff_ofFinite]
      exact FiniteLawShift.shift_coeff_zero ν
  | succ k =>
    induction ν using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (coeff k).continuous
    | ih ν =>
      change coeff (k + 1) (ofFinite (atom 1) * ofFinite ν) = coeff k (ofFinite ν)
      rw [← map_mul, coeff_ofFinite, coeff_ofFinite]
      exact FiniteLawShift.shift_coeff_succ ν k

theorem coeff_delta (ν : Space) (k : ℕ) :
    coeff k (delta * ν) = shift (fun j ↦ coeff j ν) k - coeff k ν := by
  rw [delta, forwardDifference, map_sub, sub_mul, atom_zero, map_one, one_mul,
    map_sub, coeff_shift]

theorem coeff_delta_squared (ν : Space) (k : ℕ) :
    coeff k (delta ^ 2 * ν) = secondDifference (fun j ↦ coeff j ν) k := by
  rw [pow_two, mul_assoc]
  cases k with
  | zero => simp [coeff_delta, secondDifference]
  | succ k =>
    simp only [coeff_delta, shift_succ, secondDifference]
    ring

theorem norm_delta_le : ‖delta‖ ≤ 2 := by
  rw [delta, norm_ofFinite]
  exact l1Norm_forwardDifference_le_two

def quadratic (μ α : ℝ) : Space := poisson μ + (α / 2) • (delta ^ 2 * poisson μ)

theorem coeff_quadratic (μ α : ℝ) (k : ℕ) :
    coeff k (quadratic μ α) = quadraticMass μ α k := by
  simp only [quadratic, map_add, map_smul, coeff_delta_squared, coeff_poisson,
    smul_eq_mul, quadraticMass]

theorem quadratic_actual_signed_measure (μ α : ℝ) :
    toSignedMeasure (quadratic μ α) = QuadraticPoisson.reference μ α := by
  unfold toSignedMeasure QuadraticPoisson.reference
  congr 1
  funext k
  exact coeff_quadratic μ α k

end PaperP1.CompletedLawShift
