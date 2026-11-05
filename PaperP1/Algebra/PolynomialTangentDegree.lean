module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.Ring

/-! # Polynomial tangent differentiation and its actual degree cost

The vector field annihilates its defining equation and preserves its ideal.
All bounds concern the actual formal polynomials, over any commutative ring.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialTangentDegree

open MvPolynomial

variable {R : Type*} [CommRing R]

theorem pderiv_degree_le {σ : Type*} (P : MvPolynomial σ R) (i : σ) :
    (pderiv i P).totalDegree ≤ P.totalDegree := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hc
  have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have he : (m + Finsupp.single i 1).sum (fun _ e ↦ e) = m.sum (fun _ e ↦ e) + 1 := by
    simp [Finsupp.sum_add_index']
  omega

def tangent (P Q : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  pderiv 1 P * pderiv 0 Q - pderiv 0 P * pderiv 1 Q

theorem tangent_self (P : MvPolynomial (Fin 2) R) : tangent P P = 0 := by
  simp only [tangent, mul_comm, sub_self]

theorem tangent_constant (P : MvPolynomial (Fin 2) R) (r : R) : tangent P (C r) = 0 := by
  simp only [tangent, pderiv_C, mul_zero, sub_zero]

theorem tangent_add (P Q T : MvPolynomial (Fin 2) R) :
    tangent P (Q + T) = tangent P Q + tangent P T := by
  simp only [tangent, map_add]
  ring

theorem tangent_mul (P Q T : MvPolynomial (Fin 2) R) :
    tangent P (Q * T) = tangent P Q * T + Q * tangent P T := by
  simp only [tangent, pderiv_mul]
  ring

theorem tangent_multiple (P Q : MvPolynomial (Fin 2) R) :
    tangent P (P * Q) = P * tangent P Q := by
  rw [tangent_mul, tangent_self, zero_mul, zero_add]

theorem tangent_degree (P Q : MvPolynomial (Fin 2) R) :
    (tangent P Q).totalDegree ≤ P.totalDegree + Q.totalDegree := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add (pderiv_degree_le P 1) (pderiv_degree_le Q 0))
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add (pderiv_degree_le P 0) (pderiv_degree_le Q 1))

theorem iterate_degree (P Q : MvPolynomial (Fin 2) R) (n : ℕ) :
    ((tangent P)^[n] Q).totalDegree ≤ Q.totalDegree + n * P.totalDegree := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, zero_mul, add_zero, le_refl]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ P.totalDegree + ((tangent P)^[n] Q).totalDegree := tangent_degree P _
      _ ≤ P.totalDegree + (Q.totalDegree + n * P.totalDegree) := Nat.add_le_add_left ih _
      _ = Q.totalDegree + (n + 1) * P.totalDegree := by ring

end PaperP1.PolynomialTangentDegree
