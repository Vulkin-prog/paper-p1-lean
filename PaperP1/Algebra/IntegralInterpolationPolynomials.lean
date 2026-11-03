module

public import PaperP1.Algebra.SmallIntegerKernelCodimensionOne
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Literal integer coefficient vectors and the rational-interpolation equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralInterpolationPolynomials

open Polynomial Finset

abbrev Column (a : ℕ) := Fin (a + 1) ⊕ Fin (a + 1)

def polynomial {a : ℕ} (w : Fin (a + 1) → ℤ) : ℤ[X] := ∑ i : Fin (a + 1), monomial (i : ℕ) (w i)

theorem polynomial_coeff {a : ℕ} (w : Fin (a + 1) → ℤ) (i : Fin (a + 1)) :
    (polynomial w).coeff i = w i := by
  simp [polynomial, coeff_monomial, ← Fin.ext_iff]

theorem polynomial_natDegree {a : ℕ} (w : Fin (a + 1) → ℤ) : (polynomial w).natDegree ≤ a := by
  have hm : polynomial w ∈ degreeLT ℤ (a + 1) :=
    Submodule.sum_mem _ (fun i _ ↦ monomial_coe_mem_degreeLT i (w i))
  rw [degreeLT_succ_eq_degreeLE] at hm
  exact natDegree_le_of_degree_le (mem_degreeLE.mp hm)

theorem polynomial_eval {a : ℕ} (w : Fin (a + 1) → ℤ) (x : ℤ) :
    (polynomial w).eval x = ∑ i, w i * x ^ (i : ℕ) := by
  change (evalRingHom x) (polynomial w) = _
  simp only [polynomial, map_sum, coe_evalRingHom, eval_monomial]

theorem polynomial_coeff_bound {a M : ℕ} (w : Fin (a + 1) → ℤ)
    (hw : ∀ i, (w i).natAbs ≤ M) (n : ℕ) : ((polynomial w).coeff n).natAbs ≤ M := by
  by_cases hn : n < a + 1
  · change ((polynomial w).coeff (⟨n, hn⟩ : Fin (a + 1))).natAbs ≤ M
    rw [polynomial_coeff]
    exact hw _
  · rw [coeff_eq_zero_of_natDegree_lt (by have := polynomial_natDegree w; omega)]
    exact Nat.zero_le M

def numerator {a : ℕ} (w : Column a → ℤ) : ℤ[X] := polynomial (fun i ↦ w (Sum.inl i))
def denominator {a : ℕ} (w : Column a → ℤ) : ℤ[X] := polynomial (fun i ↦ w (Sum.inr i))

theorem pair_ne_zero {a : ℕ} (w : Column a → ℤ) (hw : w ≠ 0) :
    numerator w ≠ 0 ∨ denominator w ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hw
  funext i
  cases i with
  | inl i =>
    have hi := polynomial_coeff (fun i ↦ w (Sum.inl i)) i
    change (numerator w).coeff i = w (Sum.inl i) at hi
    rw [h.1, coeff_zero] at hi
    exact hi.symm
  | inr i =>
    have hi := polynomial_coeff (fun i ↦ w (Sum.inr i)) i
    change (denominator w).coeff i = w (Sum.inr i) at hi
    rw [h.2, coeff_zero] at hi
    exact hi.symm

def row (a : ℕ) (x y : ℤ) : Column a → ℤ :=
  Sum.elim (fun i ↦ x ^ (i : ℕ)) (fun i ↦ -y * x ^ (i : ℕ))

theorem row_equation {a : ℕ} (w : Column a → ℤ) (x y : ℤ) :
    (∑ i, row a x y i * w i) = (numerator w).eval x - y * (denominator w).eval x := by
  rw [Fintype.sum_sum_type]
  simp only [row, Sum.elim_inl, Sum.elim_inr, numerator, denominator, polynomial_eval,
    Finset.mul_sum, neg_mul, ← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem row_height {a B : ℕ} (hB : 1 ≤ B) (x y : ℤ) (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (i : Column a) : (row a x y i).natAbs ≤ B ^ (a + 1) := by
  cases i with
  | inl i =>
    change (x ^ (i : ℕ)).natAbs ≤ _
    rw [Int.natAbs_pow]
    exact (Nat.pow_le_pow_left hx _).trans (Nat.pow_le_pow_right hB (by omega))
  | inr i =>
    change (-y * x ^ (i : ℕ)).natAbs ≤ _
    rw [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow]
    calc
      y.natAbs * x.natAbs ^ (i : ℕ) ≤ B * B ^ (i : ℕ) := Nat.mul_le_mul hy (Nat.pow_le_pow_left hx _)
      _ = B ^ ((i : ℕ) + 1) := (pow_succ' _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hB (by omega)

end PaperP1.IntegralInterpolationPolynomials
