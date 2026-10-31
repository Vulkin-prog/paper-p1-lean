module

public import PaperP1.Probability.Convolution
public import PaperP1.Probability.SubsetFactorials
public import Mathlib.Algebra.Polynomial.Derivative

/-! # The generating polynomial after the exact substitution z=1+t -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialGeneratingPolynomial

open PaperP1.Algebra PaperP1.Probability Polynomial Finset

def baseHom : Multiplicative ℕ →* ℝ[X] where
  toFun n := (1 + X) ^ n.toAdd
  map_one' := by simp
  map_mul' _ _ := by simp only [toAdd_mul, pow_add]

def transform : SignedLaw ℝ →+* ℝ[X] :=
  AddMonoidAlgebra.liftNCRingHom C baseHom (fun _ _ ↦ Commute.all _ _)

theorem transform_single (n : ℕ) (r : ℝ) :
    transform (AddMonoidAlgebra.single n r) = C r * (1 + X) ^ n := by
  rw [transform, AddMonoidAlgebra.liftNCRingHom_single]
  rfl

theorem transform_atom (n : ℕ) : transform (atom n) = (1 + X) ^ n := by
  rw [atom, transform_single, C_1, one_mul]

theorem transform_scalar (r : ℝ) : transform (scalar r) = C r := by
  rw [scalar_apply, transform_single, pow_zero, mul_one]

theorem transform_forwardDifference : transform forwardDifference = X := by
  rw [forwardDifference, map_sub, transform_atom, transform_atom]
  simp

def ordinaryPolynomial (ν : SignedLaw ℝ) : ℝ[X] :=
  ν.coeff.sum fun k c ↦ C c * X ^ k

theorem transform_eq_sum (ν : SignedLaw ℝ) :
    transform ν = ν.coeff.sum fun k c ↦ C c * (1 + X) ^ k := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
  simp only [Finsupp.sum, map_sum, transform_single]

theorem transform_eq_comp (ν : SignedLaw ℝ) :
    transform ν = (ordinaryPolynomial ν).comp (1 + X) := by
  rw [transform_eq_sum]
  unfold ordinaryPolynomial Finsupp.sum
  rw [Polynomial.sum_comp]
  apply sum_congr rfl
  intro k _
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]

variable {Ω ι : Type*} [Fintype Ω]

def jointMoment (w : Ω → ℝ) (J : ι → Ω → Bool) (I : Finset ι) : ℝ :=
  finiteExpectation w (fun ω ↦ ∏ x ∈ I, indicatorValue (J x ω))

theorem transform_countLaw (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    transform (countLaw G w J) = ∑ ω, C (w ω) * (1 + X) ^ indicatorCount G J ω := by
  simp only [countLaw, map_sum, map_mul, transform_scalar, transform_atom]

theorem transform_countLaw_coeff (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) (j : ℕ) :
    (transform (countLaw G w J)).coeff j =
      finiteExpectation w (fun ω ↦ ((indicatorCount G J ω).choose j : ℝ)) := by
  rw [transform_countLaw]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  rfl

theorem countLaw_uncentered_expansion [DecidableEq ι] (G : Finset ι)
    (w : Ω → ℝ) (J : ι → Ω → Bool) :
    countLaw G w J = ∑ I ∈ G.powerset, scalar (jointMoment w J I) * forwardDifference ^ I.card := by
  have h := centered_countLaw_expansion G w J (fun _ ↦ 0)
  simpa only [centeredMoment, sub_zero, jointMoment, bernoulli, map_zero, zero_mul,
    add_zero, atom_zero, prod_const_one, mul_one] using h

theorem transform_countLaw_subset_coeff (G : Finset ι) (w : Ω → ℝ)
    (J : ι → Ω → Bool) (j : ℕ) :
    (transform (countLaw G w J)).coeff j = ∑ I ∈ G.powersetCard j, jointMoment w J I := by
  rw [transform_countLaw_coeff]
  simp_rw [jointMoment, ← finiteExpectation_sum, sum_subset_products_eq_choose]

end PaperP1.FactorialGeneratingPolynomial
