module

public import PaperP1.Algebra.HomogeneousQuadraticHessian
public import PaperP1.Algebra.IntegerRowWeightDeterminant
public import Mathlib.Tactic.Linarith

/-! # Explicit cubic heights for the actual integer quadratic Hessian minors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadricHessianMinorHeight

open MvPolynomial HomogeneousQuadraticHessian

def minor (P : MvPolynomial (Fin 4) ℤ) (r c : Fin 3 → Fin 4) : ℤ :=
  Matrix.det (fun i j ↦ entry P (r i) (c j))

def certificate (P : MvPolynomial (Fin 4) ℤ) (r c : Fin 3 → Fin 4) : ℤ :=
  2 * minor P r c

theorem entry_bound {σ : Type*} (A : ℕ) (P : MvPolynomial σ ℤ)
    (hP : ∀ m, |P.coeff m| ≤ (A : ℤ)) (i j : σ) : |entry P i j| ≤ 2 * (A : ℤ) := by
  have hh := hP (Finsupp.single i 1 + Finsupp.single j 1)
  have hA : (0 : ℤ) ≤ A := Nat.cast_nonneg A
  rw [coefficient_formula]
  split_ifs
  · rw [abs_mul, show |(2 : ℤ)| = 2 by decide]
    linarith
  · rw [mul_one]
    linarith

theorem minor_bound (A : ℕ) (P : MvPolynomial (Fin 4) ℤ)
    (hP : ∀ m, |P.coeff m| ≤ (A : ℤ)) (r c : Fin 3 → Fin 4) :
    (minor P r c).natAbs ≤ 48 * A ^ 3 := by
  have hb := IntegerRowWeightDeterminant.natAbs_bound
    (fun i j : Fin 3 ↦ entry P (r i) (c j)) (fun _ ↦ 2 * A) (by
      intro i j
      exact_mod_cast entry_bound A P hP (r i) (c j))
  calc
    _ ≤ 6 * (2 * A) ^ 3 := by simpa only [minor, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ, show Nat.factorial 3 = 6 by decide] using hb
    _ = _ := by ring

theorem certificate_bound (A : ℕ) (P : MvPolynomial (Fin 4) ℤ)
    (hP : ∀ m, |P.coeff m| ≤ (A : ℤ)) (r c : Fin 3 → Fin 4) :
    (certificate P r c).natAbs ≤ 96 * A ^ 3 := by
  rw [certificate, Int.natAbs_mul]
  have hb := Nat.mul_le_mul_left 2 (minor_bound A P hP r c)
  rw [show (2 : ℤ).natAbs = 2 by decide]
  calc
    _ ≤ 2 * (48 * A ^ 3) := hb
    _ = _ := by ring

theorem certificate_nonzero (P : MvPolynomial (Fin 4) ℤ) (r c : Fin 3 → Fin 4)
    (h : minor P r c ≠ 0) : certificate P r c ≠ 0 :=
  mul_ne_zero (by decide) h

theorem prime_not_dvd_minor (P : MvPolynomial (Fin 4) ℤ) (r c : Fin 3 → Fin 4)
    (p : ℕ) (h : ¬(p : ℤ) ∣ certificate P r c) : ¬(p : ℤ) ∣ minor P r c :=
  fun hd ↦ h (dvd_mul_of_dvd_right hd 2)

theorem prime_ne_two (P : MvPolynomial (Fin 4) ℤ) (r c : Fin 3 → Fin 4)
    (p : ℕ) (h : ¬(p : ℤ) ∣ certificate P r c) : p ≠ 2 := by
  intro hp
  apply h
  rw [hp]
  exact dvd_mul_right _ _

end PaperP1.QuadricHessianMinorHeight
