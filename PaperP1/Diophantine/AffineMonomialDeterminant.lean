module

public import PaperP1.Algebra.SmoothCurveDeterminant
public import PaperP1.Diophantine.ProjectiveDeterminantVanishing
public import PaperP1.Analysis.DeterminantDenominatorBudget

/-! # Exact monomial weights for actual affine integer point determinants

No projective denominator is present. The size estimate keeps the actual row
weight rather than replacing every row by the largest monomial weight.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineMonomialDeterminant

open Polynomial Finset DeterminantIntegerRows

def weightSum (A J : ℕ) : ℕ := ∑ i : Exponent A J, (i.1.val + i.2.val)

def entry (z : ℤ × ℤ) (i : ℕ × ℕ) : ℤ := z.1 ^ i.1 * z.2 ^ i.2

def matrix (A J : ℕ) (z : Exponent A J → ℤ × ℤ) : Matrix (Exponent A J) (Exponent A J) ℤ :=
  fun i j ↦ entry (z j) (i.1.val, i.2.val)

theorem weight_sum_twice (A J : ℕ) :
    2 * weightSum A J = ((A + 1) * (J + 1)) * (A + J) := by
  have he : ((weightSum A J : ℕ) : ℝ) =
      (((A + 1) * (J + 1) : ℕ) : ℝ) * ((A : ℝ) + J) / 2 := by
    simp only [weightSum, Nat.cast_sum, Nat.cast_add, sum_add_distrib]
    rw [DeterminantDenominatorBudget.sum_first_exponents,
      DeterminantDenominatorBudget.sum_second_exponents]
    ring
  have hh : (2 : ℝ) * (weightSum A J : ℝ) =
      (((A + 1) * (J + 1) : ℕ) : ℝ) * ((A : ℝ) + J) := by linarith
  exact_mod_cast hh

theorem determinant_bound (A J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (z : Exponent A J → ℤ × ℤ)
    (hx : ∀ j, |((z j).1 : ℝ)| ≤ B) (hy : ∀ j, |((z j).2 : ℝ)| ≤ B) :
    |((matrix A J z).det : ℝ)| ≤
      (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J := by
  let φ := Int.castRingHom ℝ
  let M := φ.mapMatrix (matrix A J z)
  have he : M.det = ((matrix A J z).det : ℝ) := (φ.map_det _).symm
  have hentry (i j : Exponent A J) : |M i j| ≤ B ^ (i.1.val + i.2.val) := by
    change |((entry (z j) (i.1.val, i.2.val) : ℤ) : ℝ)| ≤ _
    simp only [entry, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hx j) _)
      (pow_le_pow_left₀ (abs_nonneg _) (hy j) _) (by positivity) (pow_nonneg hB _)
  have hh := WeightedEvaluationDeterminant.row_weight_bound M
    (fun i ↦ B ^ (i.1.val + i.2.val)) hentry
  rw [he] at hh
  simpa only [Exponent, Fintype.card_prod, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum, weightSum] using hh

theorem indexed_divisor (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (A J : ℕ) (z : Exponent A J → ℤ × ℤ)
    (hx : ∀ j, (p : ℤ) ∣ (z j).1 - a) (hy : ∀ j, (p : ℤ) ∣ (z j).2 - b)
    (hz : ∀ j, G.evalEval (z j).1 (z j).2 = 0) :
    (p : ℤ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2) ∣
      (matrix A J z).det := by
  let k := Fintype.card (Exponent A J)
  let e : Exponent A J ≃ Fin k := Fintype.equivFin _
  let F : Fin k → ℤ[X][X] := fun i ↦
    monomial (e.symm i).2.val (monomial (e.symm i).1.val 1)
  have hd := SmoothCurveDeterminant.integer_smooth_dvd p k hp G a b hG hder
    (fun j ↦ (z (e.symm j)).1) (fun j ↦ (z (e.symm j)).2)
    (fun j ↦ hx (e.symm j)) (fun j ↦ hy (e.symm j)) (fun j ↦ hz (e.symm j)) F
  have he : Matrix.reindex e e (matrix A J z) =
      (fun i j ↦ (F i).evalEval (z (e.symm j)).1 (z (e.symm j)).2) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, matrix, entry, F,
      Polynomial.evalEval, Polynomial.eval_monomial, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, one_mul]
  rw [← he, Matrix.det_reindex_self] at hd
  simpa only [k, Exponent, Fintype.card_prod, Fintype.card_fin] using hd

theorem vanishing (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (A J : ℕ) (B : ℝ) (hB : 0 ≤ B) (z : Exponent A J → ℤ × ℤ)
    (hx : ∀ j, (p : ℤ) ∣ (z j).1 - a) (hy : ∀ j, (p : ℤ) ∣ (z j).2 - b)
    (hz : ∀ j, G.evalEval (z j).1 (z j).2 = 0)
    (hxbox : ∀ j, |((z j).1 : ℝ)| ≤ B) (hybox : ∀ j, |((z j).2 : ℝ)| ≤ B)
    (hsmall : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2)) :
    (matrix A J z).det = 0 := by
  apply ProjectiveDeterminantVanishing.zero_of_dvd_small
    (p ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2))
  · simpa only [Nat.cast_pow] using indexed_divisor p hp G a b hG hder A J z hx hy hz
  · simpa only [Nat.cast_pow] using (determinant_bound A J B hB z hxbox hybox).trans_lt hsmall

end PaperP1.AffineMonomialDeterminant
