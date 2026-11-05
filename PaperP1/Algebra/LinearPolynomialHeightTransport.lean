module

public import PaperP1.Algebra.TotalDegreeMonomials

/-! # Every fixed integer-linear coefficient transformation has a finite height budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearPolynomialHeightTransport

open Polynomial Finset PaperP1.TotalDegreeMonomials PaperP1.BivariateHeight

def basis (D : ℕ) (i : Index D) : ℤ[X][X] :=
  Polynomial.monomial i.val.2.val (Polynomial.monomial i.val.1.val 1)

def budget (D : ℕ) (T : ℤ[X][X] →ₗ[ℤ] ℤ[X][X]) : ℕ := ∑ i : Index D, height (T (basis D i))

theorem height_smul (c : ℤ) (P : ℤ[X][X]) : height (c • P) ≤ c.natAbs * height P := by
  apply PolynomialHeightArithmetic.bivariate_height_le
  intro y x
  simp only [Polynomial.coeff_smul, smul_eq_mul, Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (coefficient_natAbs_le_height P y x)

theorem height_sum {ι : Type*} (S : Finset ι) (P : ι → ℤ[X][X]) :
    height (∑ i ∈ S, P i) ≤ ∑ i ∈ S, height (P i) := by
  apply PolynomialHeightArithmetic.bivariate_height_le
  intro y x
  simp only [Polynomial.finsetSum_coeff]
  exact (Int.natAbs_sum_le S _).trans
    (Finset.sum_le_sum (fun i _ ↦ coefficient_natAbs_le_height (P i) y x))

theorem expansion (D : ℕ) (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ D) :
    P = ∑ i : Index D, ((P.coeff i.val.2.val).coeff i.val.1.val) • basis D i := by
  calc
    P = polynomial D (fun i ↦ (P.coeff i.val.2.val).coeff i.val.1.val) := (reconstruction D P hD).symm
    _ = _ := by
      unfold polynomial
      apply Finset.sum_congr rfl
      intro i _
      simp only [basis, Polynomial.smul_monomial, smul_eq_mul, mul_one]

theorem linear_height (D : ℕ) (T : ℤ[X][X] →ₗ[ℤ] ℤ[X][X]) (P : ℤ[X][X])
    (hD : PlaneCurvePointCount.degree P ≤ D) : height (T P) ≤ height P * budget D T := by
  have he : T P = ∑ i : Index D, ((P.coeff i.val.2.val).coeff i.val.1.val) • T (basis D i) := by
    calc
      _ = T (∑ i : Index D, ((P.coeff i.val.2.val).coeff i.val.1.val) • basis D i) :=
        congrArg T (expansion D P hD)
      _ = _ := by rw [map_sum]; simp only [map_smul]
  rw [he]
  calc
    _ ≤ ∑ i : Index D, height (((P.coeff i.val.2.val).coeff i.val.1.val) • T (basis D i)) :=
      height_sum _ _
    _ ≤ ∑ i : Index D, ((P.coeff i.val.2.val).coeff i.val.1.val).natAbs * height (T (basis D i)) :=
      Finset.sum_le_sum (fun i _ ↦ height_smul _ _)
    _ ≤ ∑ i : Index D, height P * height (T (basis D i)) :=
      Finset.sum_le_sum (fun i _ ↦ Nat.mul_le_mul_right _ (coefficient_natAbs_le_height P _ _))
    _ = _ := by rw [budget, Finset.mul_sum]

theorem finite_family_height {ι : Type*} (D : ℕ) (S : Finset ι)
    (T : ι → ℤ[X][X] →ₗ[ℤ] ℤ[X][X]) (i : ι) (hi : i ∈ S) (P : ℤ[X][X])
    (hD : PlaneCurvePointCount.degree P ≤ D) :
    height (T i P) ≤ (S.sup (fun j ↦ budget D (T j))) * height P := by
  have hb := Finset.le_sup (f := fun j ↦ budget D (T j)) hi
  exact (linear_height D (T i) P hD).trans
    ((Nat.mul_le_mul_left (height P) hb).trans_eq (Nat.mul_comm _ _))

end PaperP1.LinearPolynomialHeightTransport
