module

public import PaperP1.Algebra.IntegralInterpolationPolynomials
public import Mathlib.Algebra.Polynomial.Roots

/-! # Integral rational-interpolation pairs with a height bound depending only on the grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralRationalInterpolation

open Polynomial Finset PaperP1.IntegralInterpolationPolynomials

def heightBound (a B : ℕ) : ℕ := (3 * ((2 * a + 1) + 1) * B ^ (a + 1)) ^ (2 * a + 1)

theorem heightBound_eq (a B : ℕ) : heightBound a B =
    (3 * ((2 * a + 1) + 1)) ^ (2 * a + 1) * B ^ ((a + 1) * (2 * a + 1)) := by
  rw [heightBound, mul_pow, ← pow_mul]

theorem exists_pair (a B : ℕ) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B) :
    ∃ P Q : ℤ[X], (P ≠ 0 ∨ Q ≠ 0) ∧ P.natDegree ≤ a ∧ Q.natDegree ≤ a ∧
      (∀ n, (P.coeff n).natAbs ≤ heightBound a B) ∧
      (∀ n, (Q.coeff n).natAbs ≤ heightBound a B) ∧ ∀ j, P.eval (x j) = y j * Q.eval (x j) := by
  let e : Column a ≃ Fin ((2 * a + 1) + 1) := finSumFinEquiv.trans (finCongr (by omega))
  have hH : 0 < B ^ (a + 1) := pow_pos (by omega) _
  have hA : ∀ j i, |row a (x j) (y j) i| ≤ (B ^ (a + 1) : ℕ) := by
    intro j i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast row_height hB (x j) (y j) (hx j) (hy j) i
  obtain ⟨w, hw0, hw, hker⟩ := SmallIntegerKernelCodimensionOne.exists_small_kernel_equiv
    (2 * a + 1) (B ^ (a + 1)) hH e (fun j ↦ row a (x j) (y j)) hA
  have hwNat (i : Column a) : (w i).natAbs ≤ heightBound a B := by
    have hi := hw i
    rw [Int.abs_eq_natAbs] at hi
    exact_mod_cast hi
  refine ⟨numerator w, denominator w, pair_ne_zero w hw0, polynomial_natDegree _, polynomial_natDegree _,
    polynomial_coeff_bound _ (fun i ↦ hwNat (Sum.inl i)),
    polynomial_coeff_bound _ (fun i ↦ hwNat (Sum.inr i)), ?_⟩
  intro j
  apply sub_eq_zero.mp
  exact (row_equation w (x j) (y j)).symm.trans (hker j)

theorem denominator_ne_zero (a : ℕ) (x y : Fin (2 * a + 1) → ℤ)
    (hx : Function.Injective x) (P Q : ℤ[X]) (hne : P ≠ 0 ∨ Q ≠ 0) (hP : P.natDegree ≤ a)
    (hgrid : ∀ j, P.eval (x j) = y j * Q.eval (x j)) : Q ≠ 0 := by
  intro hQ
  have hP0 : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hx
    (fun j ↦ by simpa only [hQ, eval_zero, mul_zero] using hgrid j)
    (by simpa only [Fintype.card_fin] using (by omega : P.natDegree < 2 * a + 1))
  exact hne.elim (fun h ↦ h hP0) (fun h ↦ h hQ)

theorem exists_pair_nonzero_denominator (a B : ℕ) (hB : 1 ≤ B) (x y : Fin (2 * a + 1) → ℤ)
    (hinj : Function.Injective x) (hx : ∀ j, (x j).natAbs ≤ B) (hy : ∀ j, (y j).natAbs ≤ B) :
    ∃ P Q : ℤ[X], Q ≠ 0 ∧ P.natDegree ≤ a ∧ Q.natDegree ≤ a ∧
      (∀ n, (P.coeff n).natAbs ≤ heightBound a B) ∧
      (∀ n, (Q.coeff n).natAbs ≤ heightBound a B) ∧ ∀ j, P.eval (x j) = y j * Q.eval (x j) := by
  obtain ⟨P, Q, hne, hP, hQ, hpc, hqc, hgrid⟩ := exists_pair a B hB x y hx hy
  exact ⟨P, Q, denominator_ne_zero a x y hinj P Q hne hP hgrid, hP, hQ, hpc, hqc, hgrid⟩

end PaperP1.IntegralRationalInterpolation
