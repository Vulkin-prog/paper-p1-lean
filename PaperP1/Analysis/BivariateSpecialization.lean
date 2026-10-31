module

public import PaperP1.Analysis.PolynomialParsevalBounds

/-! # A bivariate factor bound through one-variable specialization

Bivariate polynomials are nested polynomials. The outer coefficient at a
fixed degree of the second factor is retained even if specialization drops
its degree. Parseval gives the exact coefficient-energy constant.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateSpecialization

open Polynomial Finset MahlerCoefficientBounds PolynomialParsevalBounds

def bivariateCoefficientEnergy (P : ℂ[X][X]) : ℝ :=
  ∑ i ∈ P.support, coefficientEnergy (P.coeff i)

def bivariateL2Norm (P : ℂ[X][X]) : ℝ := Real.sqrt (bivariateCoefficientEnergy P)

theorem bivariateCoefficientEnergy_nonneg (P : ℂ[X][X]) : 0 ≤ bivariateCoefficientEnergy P :=
  sum_nonneg fun i _ ↦ coefficientEnergy_nonneg (P.coeff i)

theorem bivariateL2Norm_nonneg (P : ℂ[X][X]) : 0 ≤ bivariateL2Norm P := Real.sqrt_nonneg _

theorem bivariateL2Norm_sq (P : ℂ[X][X]) : (bivariateL2Norm P) ^ 2 = bivariateCoefficientEnergy P :=
  Real.sq_sqrt (bivariateCoefficientEnergy_nonneg P)

def specializeInner (P : ℂ[X][X]) (z : ℂ) : ℂ[X] := P.map (evalRingHom z)

theorem specializeInner_coeff (P : ℂ[X][X]) (z : ℂ) (i : ℕ) :
    (specializeInner P z).coeff i = (P.coeff i).eval z := coeff_map (evalRingHom z) i

theorem specializeInner_mul (P Q : ℂ[X][X]) (z : ℂ) :
    specializeInner (P * Q) z = specializeInner P z * specializeInner Q z :=
  Polynomial.map_mul (evalRingHom z)

theorem specializeInner_natDegree_le (P : ℂ[X][X]) (z : ℂ) :
    (specializeInner P z).natDegree ≤ P.natDegree := natDegree_map_le

theorem coefficientEnergy_specialize (P : ℂ[X][X]) (z : ℂ) :
    coefficientEnergy (specializeInner P z) = ∑ i ∈ P.support, ‖(P.coeff i).eval z‖ ^ 2 := by
  have hsub : (specializeInner P z).support ⊆ P.support := support_map_subset (evalRingHom z) P
  calc
    _ = ∑ i ∈ P.support, ‖(specializeInner P z).coeff i‖ ^ 2 := by
      apply sum_subset hsub
      intro i _ hi
      rw [notMem_support_iff.mp hi]
      norm_num
    _ = _ := by simp only [specializeInner_coeff]

theorem factor_pointwise_sq (Q R : ℂ[X][X]) (D E i : ℕ)
    (hQ : Q.natDegree ≤ D) (hR : R.natDegree ≤ E) (z : ℂ) :
    ‖(Q.coeff i * R.coeff E).eval z‖ ^ 2 ≤ ((2 : ℝ) ^ D) ^ 2 *
      ∑ j ∈ (Q * R).support, ‖((Q * R).coeff j).eval z‖ ^ 2 := by
  have h := factor_coefficient_product_bound_two_pow (specializeInner Q z) (specializeInner R z)
    D E i ((specializeInner_natDegree_le Q z).trans hQ) ((specializeInner_natDegree_le R z).trans hR)
  simp only [specializeInner_coeff, ← specializeInner_mul] at h
  rw [← eval_mul] at h
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, l2CoefficientNorm_sq, coefficientEnergy_specialize] using hsquare

theorem factor_outer_coefficient_l2_bound (Q R : ℂ[X][X]) (D E i : ℕ)
    (hQ : Q.natDegree ≤ D) (hR : R.natDegree ≤ E) :
    l2CoefficientNorm (Q.coeff i * R.coeff E) ≤ (2 : ℝ) ^ D * bivariateL2Norm (Q * R) :=
  l2_le_of_pointwise_bound _ (Q * R).support (fun j ↦ (Q * R).coeff j) ((2 : ℝ) ^ D)
    (by positivity) (factor_pointwise_sq Q R D E i hQ hR)

end PaperP1.BivariateSpecialization
