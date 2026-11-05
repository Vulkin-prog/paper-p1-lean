module

public import PaperP1.Algebra.BoundedFieldPolynomialNonvanishing
public import PaperP1.Algebra.CommonLinearNormalization
public import Mathlib.Algebra.Polynomial.BigOperators

/-! # Bounded integer coefficients avoiding every vector in an actual finite nonzero family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedMomentLinearForm

open Polynomial Finset

def moment {F : Type*} [Semiring F] {n : ℕ} (w : Fin n → F) : F[X] :=
  ∑ i, Polynomial.monomial i.val (w i)

theorem coefficient {F : Type*} [Semiring F] {n : ℕ} (w : Fin n → F) (i : Fin n) :
    (moment w).coeff i.val = w i := by
  classical
  simp [moment, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]

theorem degree {F : Type*} [Semiring F] {n : ℕ} (w : Fin n → F) :
    (moment w).natDegree ≤ n - 1 := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  exact (Polynomial.natDegree_monomial_le _).trans (by have hh := i.isLt; omega)

theorem nonzero {F : Type*} [Semiring F] {n : ℕ} (w : Fin n → F) (hw : w ≠ 0) : moment w ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hh
    exact hw (funext hh)
  intro hz
  have he := coefficient w i
  rw [hz, Polynomial.coeff_zero] at he
  exact hi he.symm

theorem evaluation {F : Type*} [Semiring F] {n : ℕ} (w : Fin n → F) (t : F) :
    (moment w).eval t = ∑ i, w i * t ^ i.val := by
  classical
  simp [moment, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem exists_parameter {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (S : Finset (Fin n → F)) (hne : ∀ w ∈ S, w ≠ 0) :
    ∃ t : ℕ, t ≤ (n - 1) * S.card ∧ ∀ w ∈ S, (moment w).eval (t : F) ≠ 0 := by
  classical
  let P : F[X] := ∏ w ∈ S, moment w
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w hw ↦ nonzero w (hne w hw))
  have hdegree : P.natDegree ≤ (n - 1) * S.card := by
    calc
      _ ≤ ∑ w ∈ S, (moment w).natDegree := Polynomial.natDegree_prod_le S _
      _ ≤ ∑ _w ∈ S, (n - 1) := Finset.sum_le_sum (fun w _ ↦ degree w)
      _ = _ := by simp [mul_comm]
  obtain ⟨t, ht, hval⟩ := BoundedFieldPolynomialNonvanishing.exists_nat_nonroot P hP _ hdegree
  refine ⟨t, ht, ?_⟩
  have hprod : ∏ w ∈ S, (moment w).eval (t : F) ≠ 0 := by simpa only [P, eval_prod] using hval
  exact Finset.prod_ne_zero_iff.mp hprod

theorem exists_coefficients {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (S : Finset (Fin n → F)) (hne : ∀ w ∈ S, w ≠ 0) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * S.card + 1) ^ (n - 1)) ∧
      ∀ w ∈ S, MvPolynomial.eval w (CommonLinearNormalization.form (fun i ↦ (u i : F))) ≠ 0 := by
  obtain ⟨t, ht, hnonzero⟩ := exists_parameter n S hne
  let M := (n - 1) * S.card
  let u : Fin n → ℕ := fun i ↦ t ^ i.val
  refine ⟨u, ?_, ?_⟩
  · intro i
    calc
      _ ≤ (M + 1) ^ i.val := Nat.pow_le_pow_left (by dsimp [M]; omega) _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by have hh := i.isLt; omega)
  · intro w hw
    have he : MvPolynomial.eval w (CommonLinearNormalization.form (fun i ↦ (u i : F))) =
        (moment w).eval (t : F) := by
      rw [CommonLinearNormalization.evaluation, evaluation]
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp [u]
      rw [Nat.cast_pow, mul_comm]
    rw [he]
    exact hnonzero w hw

end PaperP1.BoundedMomentLinearForm
