module

public import PaperP1.Algebra.LastChartPolynomial
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Weight

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearPolynomialSubstitutionDegree

open MvPolynomial Finset

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Fintype σ]

theorem monomial_bound (φ : R →+* S) (Y : σ → MvPolynomial τ S)
    (hY : ∀ i, (Y i).totalDegree ≤ 1) (m : σ →₀ ℕ) (c : R) :
    (eval₂Hom (C.comp φ) Y (monomial m c)).totalDegree ≤ m.degree := by
  classical
  rw [coe_eval₂Hom, eval₂_monomial, RingHom.comp_apply]
  have hprod : (m.prod (fun i e ↦ Y i ^ e)).totalDegree ≤ m.degree := by
    rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.degree_eq_sum]
    apply (totalDegree_finsetProd univ (fun i ↦ Y i ^ m i)).trans
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow (Y i) (m i)).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m i) (hY i))
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hprod)

theorem substitution_bound (φ : R →+* S) (Y : σ → MvPolynomial τ S)
    (hY : ∀ i, (Y i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) Y P).totalDegree ≤ P.totalDegree := by
  classical
  have hs : eval₂Hom (C.comp φ) Y P =
      ∑ m ∈ P.support, eval₂Hom (C.comp φ) Y (monomial m (P.coeff m)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [hs]
  apply totalDegree_finsetSum_le
  intro m hm
  exact (monomial_bound φ Y hY m (P.coeff m)).trans (le_totalDegree hm)

end PaperP1.LinearPolynomialSubstitutionDegree
