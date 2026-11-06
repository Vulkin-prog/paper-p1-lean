module

public import PaperP1.Algebra.SurfaceEvaluationDeterminantDivisibility
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

/-! # Actual two-variable polynomial evaluation determinants have the proved surface divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariatePolynomialDeterminantDivisibility

open MvPolynomial Finset WeightedEvaluationDeterminant

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem polynomial_dvd (p : R) (P : ι → MvPolynomial (Fin 2) R) (L : ℕ) (x y : ι → R)
    (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ Matrix.det (fun i j ↦ eval ![x j, y j] (P i)) := by
  classical
  let S := (univ : Finset ι).biUnion fun i ↦ (P i).support
  let m : S → ℕ × ℕ := fun r ↦ (r.val 0, r.val 1)
  have hm : Function.Injective m := by
    intro r s hrs
    apply Subtype.ext
    ext t
    fin_cases t
    · exact congrArg Prod.fst hrs
    · exact congrArg Prod.snd hrs
  let C : ι → S → R := fun i r ↦ (P i).coeff r.val
  have he : evaluationMatrix C (fun r j ↦ x j ^ (m r).1 * y j ^ (m r).2) =
      (fun i j ↦ eval ![x j, y j] (P i)) := by
    ext i j
    change (∑ r : S, (P i).coeff r.val * (x j ^ r.val 0 * y j ^ r.val 1)) = _
    rw [Finset.sum_coe_sort S (fun r : Fin 2 →₀ ℕ ↦ (P i).coeff r * (x j ^ r 0 * y j ^ r 1)),
      MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsub : (P i).support ⊆ S := by
      intro r hr
      exact mem_biUnion.mpr ⟨i, mem_univ i, hr⟩
    apply (Finset.sum_subset hsub ?_).symm
    intro r _hr hnot
    have hz : (P i).coeff r = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using hnot
    rw [hz, zero_mul]
  rw [← he]
  exact SurfaceEvaluationDeterminantDivisibility.monomial_dvd p C m hm L x y hx hy

theorem congruent_polynomial_dvd (p : R) (P : ι → MvPolynomial (Fin 2) R) (L : ℕ) (x y : ι → R)
    (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) (A : Matrix ι ι R)
    (hA : ∀ i j, p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A i j - eval ![x j, y j] (P i)) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A.det := by
  have hd := FilteredEvaluationDeterminantDivisibility.determinant_congruence_dvd
    (p ^ (L * Fintype.card ι - (L + 2).choose 3)) A (fun i j ↦ eval ![x j, y j] (P i)) hA
  have hh := dvd_add hd (polynomial_dvd p P L x y hx hy)
  simpa only [sub_add_cancel] using hh

end PaperP1.BivariatePolynomialDeterminantDivisibility
