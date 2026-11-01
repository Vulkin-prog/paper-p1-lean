module

public import PaperP1.Diophantine.ResultantHeight
public import PaperP1.Diophantine.BivariateGridCount
public import Mathlib.Tactic.LinearCombination

/-! # Actual elimination along an auxiliary equation linear in a primitive pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BidegreeOneElimination

open Finset MvPolynomial

def scale (a b A B : ℤ) : ℤ := Int.gcdA a b * B - Int.gcdB a b * A

theorem scale_equations (a b A B : ℤ) (hab : a.natAbs.Coprime b.natAbs)
    (hrel : a * A + b * B = 0) :
    scale a b A B * a = B ∧ scale a b A B * b = -A := by
  have hbezout : a * Int.gcdA a b + b * Int.gcdB a b = 1 := by
    simpa only [Int.gcd_def, hab.gcd_eq_one, Nat.cast_one] using (Int.gcd_eq_gcd_ab a b).symm
  unfold scale
  constructor
  · linear_combination B * hbezout - Int.gcdB a b * hrel
  · linear_combination -A * hbezout + Int.gcdA a b * hrel

def original {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (v z : Fin 2 → ℤ) : ℤ :=
  ∑ i, eval z (C i) * v 0 ^ i.val * v 1 ^ (ell - i.val)

def eliminant {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ i, C i * G ^ i.val * (-F) ^ (ell - i.val)

theorem monomial_scale (q a b c : ℤ) (ell i : ℕ) (hi : i ≤ ell) :
    c * (q * a) ^ i * (q * b) ^ (ell - i) =
      q ^ ell * (c * a ^ i * b ^ (ell - i)) := by
  rw [mul_pow, mul_pow]
  calc
    _ = (q ^ i * q ^ (ell - i)) * (c * a ^ i * b ^ (ell - i)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hi]

theorem eliminant_evaluation {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (v z : Fin 2 → ℤ) (q : ℤ)
    (hfirst : q * v 0 = eval z G) (hsecond : q * v 1 = -eval z F) :
    eval z (eliminant C F G) = q ^ ell * original C v z := by
  simp only [eliminant, original, MvPolynomial.eval_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [map_mul, map_pow, map_neg]
  rw [← hfirst, ← hsecond]
  exact monomial_scale q (v 0) (v 1) (eval z (C i)) ell i.val (by have := i.isLt; omega)

theorem eliminant_homogeneous {ell k d : ℕ}
    (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ) (F G : MvPolynomial (Fin 2) ℤ)
    (hC : ∀ i, (C i).IsHomogeneous k) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) :
    (eliminant C F G).IsHomogeneous (k + d * ell) := by
  apply IsHomogeneous.sum
  intro i _
  have hi : i.val ≤ ell := by have := i.isLt; omega
  have h := ((hC i).mul (hG.pow i.val)).mul (hF.neg.pow (ell - i.val))
  have hdeg : (k + d * i.val) + d * (ell - i.val) = k + d * ell := by
    rw [add_assoc, ← Nat.mul_add, Nat.add_sub_of_le hi]
  simpa only [hdeg] using h

theorem eliminant_equation {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (v z : Fin 2 → ℤ) (q h : ℤ)
    (hfirst : q * v 0 = eval z G) (hsecond : q * v 1 = -eval z F) (heq : original C v z = h) :
    eval z (eliminant C F G) = q ^ ell * h := by
  rw [eliminant_evaluation C F G v z q hfirst hsecond, heq]

theorem level_box_bound {ell k d : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (hC : ∀ i, (C i).IsHomogeneous k)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) (hdegree : 0 < k + d * ell)
    (q h : ℤ) (hq : q ≠ 0) (hh : h ≠ 0) (H : ℕ) :
    (PaperP1.BivariateGridCount.level (eliminant C F G) (q ^ ell * h) (Finset.Icc (-(H : ℤ)) H)).card ≤
      (k + d * ell) * (2 * H + 1) :=
  PaperP1.BivariateGridCount.homogeneous_integer_box_bound _ _ hdegree
    (eliminant_homogeneous C F G hC hF hG) _ (mul_ne_zero (pow_ne_zero _ hq) hh) H

end PaperP1.BidegreeOneElimination
