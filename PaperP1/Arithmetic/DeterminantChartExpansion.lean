module

public import PaperP1.Arithmetic.DeterminantIntegerRows
public import PaperP1.Algebra.WeightedEvaluationDeterminant
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Exact finite polynomial expansion of the relative quadratic chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantChartExpansion

open Finset PaperP1.DeterminantIntegerRows

def coefficient (a b k j : ℕ) : ℕ := b.choose j * (a + 2 * (b - j)).choose k

theorem add_pow_finite (n K : ℕ) (hn : n ≤ K) (x y : ℝ) :
    (x + y) ^ n = ∑ k : Fin (K + 1), x ^ k.val * y ^ (n - k.val) * (n.choose k.val : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ x ^ k * y ^ (n - k) * (n.choose k : ℝ))]
  rw [add_pow]
  apply sum_subset (range_mono (Nat.add_le_add_right hn 1))
  intro k hk hkn
  have hnlt : n < k := by simp only [mem_range] at hk hkn; omega
  rw [Nat.choose_eq_zero_of_lt hnlt, Nat.cast_zero, mul_zero]

theorem one_add_pow_finite (n K : ℕ) (hn : n ≤ K) (x : ℝ) :
    (1 + x) ^ n = ∑ k : Fin (K + 1), (n.choose k.val : ℝ) * x ^ k.val := by
  rw [add_comm 1 x, add_pow_finite n K hn]
  simp only [one_pow, mul_one, mul_comm]

theorem exact_expansion (A B a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) (α β : ℝ) :
    (1 + α) ^ a * (1 + 2 * α + α ^ 2 + β) ^ b =
      ∑ k : Exponent (A + 2 * B) B,
        (coefficient a b k.1.val k.2.val : ℝ) * α ^ k.1.val * β ^ k.2.val := by
  have hcurve : 1 + 2 * α + α ^ 2 + β = β + (1 + α) ^ 2 := by ring
  rw [hcurve, add_pow_finite b B hb, mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  have hd : a + 2 * (b - j.val) ≤ A + 2 * B := by omega
  calc
    (1 + α) ^ a * (β ^ j.val * ((1 + α) ^ 2) ^ (b - j.val) * (b.choose j.val : ℝ)) =
        (b.choose j.val : ℝ) * β ^ j.val * (1 + α) ^ (a + 2 * (b - j.val)) := by
          rw [pow_add, pow_mul]
          ring
    _ = _ := by
      rw [one_add_pow_finite _ (A + 2 * B) hd, mul_sum]
      apply sum_congr rfl
      intro k _
      simp only [coefficient, Nat.cast_mul]
      ring

theorem coefficient_bound (A B a b k j : ℕ) (ha : a ≤ A) (hb : b ≤ B) :
    coefficient a b k j ≤ 2 ^ (A + 3 * B) := by
  calc
    _ ≤ 2 ^ b * 2 ^ (a + 2 * (b - j)) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ ≤ 2 ^ B * 2 ^ (A + 2 * B) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hb)
        (Nat.pow_le_pow_right (by omega) (by omega))
    _ = _ := by rw [← pow_add]; congr 1; omega

def coefficientMatrix (A B : ℕ) : Exponent A B → Exponent (A + 2 * B) B → ℝ :=
  fun i k ↦ (coefficient i.1.val i.2.val k.1.val k.2.val : ℝ)

def monomialRows {ι : Type*} (A B : ℕ) (α β : ι → ℝ) :
    Exponent (A + 2 * B) B → ι → ℝ :=
  fun k j ↦ α j ^ k.1.val * β j ^ k.2.val

theorem matrix_entry (A B : ℕ) (α β : Exponent A B → ℝ) (i j : Exponent A B) :
    WeightedEvaluationDeterminant.evaluationMatrix (coefficientMatrix A B) (monomialRows A B α β) i j =
      (1 + α j) ^ i.1.val * (1 + 2 * α j + α j ^ 2 + β j) ^ i.2.val := by
  simpa only [WeightedEvaluationDeterminant.evaluationMatrix, Matrix.of_apply,
    coefficientMatrix, monomialRows, mul_assoc] using
    (exact_expansion A B i.1.val i.2.val (by have := i.1.isLt; omega)
    (by have := i.2.isLt; omega) (α j) (β j)).symm

theorem matrix_coefficient_bound (A B : ℕ) (i : Exponent A B) (k : Exponent (A + 2 * B) B) :
    |coefficientMatrix A B i k| ≤ (2 : ℝ) ^ (A + 3 * B) := by
  rw [coefficientMatrix, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast coefficient_bound A B i.1.val i.2.val k.1.val k.2.val
    (by have := i.1.isLt; omega) (by have := i.2.isLt; omega)

end PaperP1.DeterminantChartExpansion
