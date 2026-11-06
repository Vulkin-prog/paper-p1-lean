module

public import PaperP1.Algebra.ClassifiedSurfaceDeterminantBudget
public import PaperP1.Algebra.BivariatePolynomialDeterminantDivisibility

/-! # Distinct surface classes contribute additively to one actual polynomial evaluation determinant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassifiedBivariateDeterminant

open MvPolynomial Finset WeightedEvaluationDeterminant

variable {R ι χ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype χ] [DecidableEq χ]

theorem polynomial_dvd (p : R) (P : χ → ι → MvPolynomial (Fin 2) R) (b : ι → χ)
    (L : χ → ℕ) (x y : ι → R) (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) :
    p ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ∣
      Matrix.det (fun i j ↦ eval ![x j, y j] (P (b j) i)) := by
  classical
  let S := (univ : Finset χ).biUnion fun c ↦ (univ : Finset ι).biUnion fun i ↦ (P c i).support
  let m : χ × S → ℕ × ℕ := fun r ↦ (r.2.val 0, r.2.val 1)
  let a : χ × S → χ := Prod.fst
  have hm : Function.Injective (fun r ↦ (a r, m r)) := by
    intro r s he
    apply Prod.ext
    · exact congrArg (fun t : χ × (ℕ × ℕ) ↦ t.1) he
    · apply Subtype.ext
      ext k
      fin_cases k
      · exact congrArg (fun t : χ × (ℕ × ℕ) ↦ t.2.1) he
      · exact congrArg (fun t : χ × (ℕ × ℕ) ↦ t.2.2) he
  let C : ι → χ × S → R := fun i r ↦ (P r.1 i).coeff r.2.val
  let V : χ × S → ι → R := fun r j ↦
    if r.1 = b j then x j ^ (m r).1 * y j ^ (m r).2 else 0
  have he : evaluationMatrix C V = (fun i j ↦ eval ![x j, y j] (P (b j) i)) := by
    ext i j
    change (∑ r : χ × S, (P r.1 i).coeff r.2.val *
      (if r.1 = b j then x j ^ (m r).1 * y j ^ (m r).2 else 0)) = _
    rw [Fintype.sum_prod_type]
    have hs : (∑ c : χ, ∑ r : S, (P c i).coeff r.val *
        (if c = b j then x j ^ r.val 0 * y j ^ r.val 1 else 0)) =
        ∑ r : S, (P (b j) i).coeff r.val * (x j ^ r.val 0 * y j ^ r.val 1) := by
      simp only [mul_ite, mul_zero]
      simp
    change (∑ c : χ, ∑ r : S, (P c i).coeff r.val *
      (if c = b j then x j ^ r.val 0 * y j ^ r.val 1 else 0)) = _
    rw [hs, Finset.sum_coe_sort S (fun r : Fin 2 →₀ ℕ ↦
      (P (b j) i).coeff r * (x j ^ r 0 * y j ^ r 1)), MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsub : (P (b j) i).support ⊆ S := by
      intro r hr
      exact mem_biUnion.mpr ⟨b j, mem_univ _, mem_biUnion.mpr ⟨i, mem_univ _, hr⟩⟩
    apply (Finset.sum_subset hsub ?_).symm
    intro r _ hr
    have hz : (P (b j) i).coeff r = 0 := by
      simpa only [MvPolynomial.mem_support_iff, not_not] using hr
    rw [hz, zero_mul]
  rw [← he]
  apply ClassifiedSurfaceDeterminantBudget.evaluation_dvd p C V a m hm b L
  · intro r j
    dsimp only [V]
    split_ifs
    · obtain ⟨u, hu⟩ := hx j
      obtain ⟨v, hv⟩ := hy j
      refine ⟨u ^ (m r).1 * v ^ (m r).2, ?_⟩
      rw [hu, hv, mul_pow, mul_pow, pow_add]
      ring
    · exact dvd_zero _
  · intro r j hne
    exact ite_eq_right hne

theorem congruent_polynomial_dvd (p : R) (P : χ → ι → MvPolynomial (Fin 2) R)
    (b : ι → χ) (L : χ → ℕ) (x y : ι → R)
    (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) (A : Matrix ι ι R)
    (hA : ∀ i j, p ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ∣
      A i j - eval ![x j, y j] (P (b j) i)) :
    p ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ∣ A.det := by
  have hd := FilteredEvaluationDeterminantDivisibility.determinant_congruence_dvd
    (p ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3))) A
    (fun i j ↦ eval ![x j, y j] (P (b j) i)) hA
  simpa only [sub_add_cancel] using dvd_add hd (polynomial_dvd p P b L x y hx hy)

end PaperP1.ClassifiedBivariateDeterminant
