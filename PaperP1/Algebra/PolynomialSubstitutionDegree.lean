module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight

/-! # Exact total-degree bounds for actual polynomial coefficient substitutions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialSubstitutionDegree

open MvPolynomial Finset
open scoped Classical

theorem eval2_bound {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (M : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ M) (P : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g P).totalDegree ≤ M * P.totalDegree := by
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.comp_apply, totalDegree_C, zero_add]
  calc
    (m.prod (fun i k ↦ g i ^ k)).totalDegree ≤ ∑ i ∈ m.support, (g i ^ m i).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, M * m i := by
      apply sum_le_sum
      intro i _
      exact ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))).trans_eq (Nat.mul_comm _ _)
    _ = M * m.degree := by rw [← mul_sum, Finsupp.degree_apply]
    _ ≤ M * P.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree hm)

theorem aeval_bound {R σ τ : Type*} [CommSemiring R]
    (g : σ → MvPolynomial τ R) (M : ℕ) (hg : ∀ i, (g i).totalDegree ≤ M)
    (P : MvPolynomial σ R) : (aeval g P).totalDegree ≤ M * P.totalDegree := by
  exact eval2_bound (RingHom.id R) g M hg P

end PaperP1.PolynomialSubstitutionDegree
