module

public import PaperP1.Analysis.MonomialUnitJetBounds
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int

/-! # Exact integer separation of actual normalized grid monomial determinants

Clearing each row retains its actual monomial degree. A nonzero integer
minor has absolute value at least one, independently of all coefficients.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonGridMonomialDeterminant

open MvPolynomial Finset TotalDegreeMonomials TotalDegreeMonomialFamily


def weight {n k : ℕ} (e : Fin n → Index k) : ℕ :=
  ∑ i, ((e i).val.1.val + (e i).val.2.val)

def integerMatrix {n k : ℕ} (e : Fin n → Index k) (z : Fin n → Fin 2 → ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ z j 0 ^ (e i).val.1.val * z j 1 ^ (e i).val.2.val

def normalizedMatrix {n k : ℕ} (e : Fin n → Index k) (N : ℕ) (z : Fin n → Fin 2 → ℤ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ eval (fun a ↦ (z j a : ℝ) / N) (basis (e i))

theorem weight_bound (n k : ℕ) (e : Fin n → Index k) : weight e ≤ k * n := by
  calc
    _ ≤ ∑ _i : Fin n, k := sum_le_sum (fun i _hi ↦ (e i).property)
    _ = k * n := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

theorem entry_clearing (n k N : ℕ) (hN : 0 < N) (e : Fin n → Index k)
    (z : Fin n → Fin 2 → ℤ) (i j : Fin n) :
    (N : ℝ) ^ ((e i).val.1.val + (e i).val.2.val) * normalizedMatrix e N z i j =
      (integerMatrix e z i j : ℝ) := by
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [normalizedMatrix, MonomialUnitJetBounds.basis_evaluation, pow_add, div_pow, div_pow]
  simp only [integerMatrix, Int.cast_mul, Int.cast_pow]
  field_simp

theorem determinant_clearing (n k N : ℕ) (hN : 0 < N) (e : Fin n → Index k)
    (z : Fin n → Fin 2 → ℤ) :
    ((integerMatrix e z).det : ℝ) = (N : ℝ) ^ weight e * (normalizedMatrix e N z).det := by
  let castMap := Int.castRingHom ℝ
  have he : castMap.mapMatrix (integerMatrix e z) = Matrix.of (fun i j ↦
      (N : ℝ) ^ ((e i).val.1.val + (e i).val.2.val) * normalizedMatrix e N z i j) := by
    ext i j
    exact (entry_clearing n k N hN e z i j).symm
  change castMap ((integerMatrix e z).det) = _
  rw [castMap.map_det, he, Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]
  rfl

theorem zero_of_small (n k N : ℕ) (hN : 0 < N) (e : Fin n → Index k)
    (z : Fin n → Fin 2 → ℤ)
    (hsmall : (N : ℝ) ^ weight e * |(normalizedMatrix e N z).det| < 1) :
    (normalizedMatrix e N z).det = 0 := by
  have hclearing := determinant_clearing n k N hN e z
  have hZ : (integerMatrix e z).det = 0 := by
    by_contra hne
    have hgap : (1 : ℝ) ≤ |((integerMatrix e z).det : ℝ)| := by
      exact_mod_cast Int.one_le_abs hne
    rw [hclearing, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)] at hgap
    exact (not_lt_of_ge hgap) hsmall
  have hz : ((integerMatrix e z).det : ℝ) = 0 := by rw [hZ, Int.cast_zero]
  rw [hclearing] at hz
  have hp : (N : ℝ) ^ weight e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  exact (mul_eq_zero.mp hz).resolve_left hp

end PaperP1.CommonGridMonomialDeterminant
