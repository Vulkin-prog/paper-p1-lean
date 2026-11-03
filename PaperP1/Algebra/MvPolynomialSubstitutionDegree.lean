module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # The actual total-degree bound under a bounded-degree polynomial substitution -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MvPolynomialSubstitutionDegree

open Finset MvPolynomial

theorem monomial_degree_le {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (x : σ → MvPolynomial τ S) (d : ℕ) (hx : ∀ i, (x i).totalDegree ≤ d)
    (a : σ →₀ ℕ) (c : R) :
    ((eval₂Hom (C.comp φ) x) (monomial a c)).totalDegree ≤ (a.sum fun _ n ↦ n) * d := by
  classical
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  have hprod : (a.prod fun i n ↦ x i ^ n).totalDegree ≤ (a.sum fun _ n ↦ n) * d := by
    rw [Finsupp.prod, Finsupp.sum]
    calc
      (∏ i ∈ a.support, x i ^ a i).totalDegree ≤ ∑ i ∈ a.support, (x i ^ a i).totalDegree :=
        totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ a.support, a i * d := sum_le_sum fun i _ ↦
        (totalDegree_pow (x i) (a i)).trans (Nat.mul_le_mul_left (a i) (hx i))
      _ = (∑ i ∈ a.support, a i) * d := (sum_mul a.support (fun i ↦ a i) d).symm
  calc
    (C (φ c) * a.prod (fun i n ↦ x i ^ n)).totalDegree ≤
        (C (φ c)).totalDegree + (a.prod fun i n ↦ x i ^ n).totalDegree := totalDegree_mul _ _
    _ ≤ (a.sum fun _ n ↦ n) * d := by simpa only [totalDegree_C, zero_add] using hprod

theorem totalDegree_eval2_le {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (x : σ → MvPolynomial τ S) (d : ℕ) (hx : ∀ i, (x i).totalDegree ≤ d)
    (P : MvPolynomial σ R) : ((eval₂Hom (C.comp φ) x) P).totalDegree ≤ P.totalDegree * d := by
  classical
  have heq := congrArg (eval₂Hom (C.comp φ) x) P.as_sum
  simp only [map_sum] at heq
  rw [heq]
  apply totalDegree_finsetSum_le
  intro a ha
  exact (monomial_degree_le φ x d hx a (P.coeff a)).trans (Nat.mul_le_mul_right d (le_totalDegree ha))

end PaperP1.MvPolynomialSubstitutionDegree
