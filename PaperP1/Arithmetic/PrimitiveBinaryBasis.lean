module

public import PaperP1.Diophantine.UnimodularBinaryCoordinates
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-! # Actual bounded integer basis completion of a primitive binary vector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveBinaryBasis

theorem bounded_bezout (p q : ℤ) (H : ℕ) (hpq : IsCoprime p q)
    (hp : |p| ≤ (H : ℤ)) (hq : |q| ≤ (H : ℤ)) :
    ∃ r s : ℤ, p * r + q * s = 1 ∧ |r| ≤ (H : ℤ) ^ 2 + 1 ∧ |s| ≤ (H : ℤ) ^ 2 + 1 := by
  obtain ⟨r, s, hbezout⟩ := hpq
  by_cases hp0 : p = 0
  · have hqs : q * s = 1 := by rw [hp0] at hbezout; nlinarith
    have hq0 : q ≠ 0 := by intro h; simp [h] at hqs
    have habs : |q| * |s| = 1 := by rw [← abs_mul, hqs, abs_one]
    have hs : |s| ≤ 1 := by
      have h := Int.one_le_abs hq0
      nlinarith [abs_nonneg s]
    refine ⟨0, s, ?_, ?_, ?_⟩
    · simpa only [mul_zero, zero_add] using hqs
    · positivity
    · nlinarith [sq_nonneg (H : ℤ)]
  · let k := s / p
    let r' := r + q * k
    let s' := s - p * k
    have hs' : s' = s % p := by
      dsimp [s', k]
      linear_combination -Int.emod_add_ediv_mul s p
    have hs0 : 0 ≤ s' := by rw [hs']; exact Int.emod_nonneg _ hp0
    have hsle : s' ≤ |p| := by rw [hs']; exact (Int.emod_lt_abs _ hp0).le
    have hnew : p * r' + q * s' = 1 := by
      dsimp [r', s']
      linear_combination hbezout
    have hprod : |p| * |r'| ≤ 1 + |q| * |p| := by
      calc
        _ = |p * r'| := (abs_mul _ _).symm
        _ = |1 - q * s'| := by congr 1; linear_combination hnew
        _ ≤ 1 + |q| * |s'| := by
          simpa only [sub_eq_add_neg, abs_one, abs_neg, abs_mul] using abs_add_le 1 (-(q * s'))
        _ ≤ _ := by rw [abs_of_nonneg hs0]; gcongr
    have hr : |r'| ≤ (H : ℤ) ^ 2 + 1 := by
      have hple := Int.one_le_abs hp0
      have hqp : |q| * |p| ≤ (H : ℤ) * H := by gcongr
      nlinarith [abs_nonneg r']
    have hs : |s'| ≤ (H : ℤ) ^ 2 + 1 := by
      rw [abs_of_nonneg hs0]
      have hH : 0 ≤ (H : ℤ) := Nat.cast_nonneg H
      nlinarith [sq_nonneg ((H : ℤ) - 1)]
    exact ⟨r', s', hnew, hr, hs⟩

def basis (p q r s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![p, -s; q, r]

def inverse (p q r s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![r, s; -q, p]

theorem basis_inverse (p q r s : ℤ) (h : p * r + q * s = 1) :
    basis p q r s * inverse p q r s = 1 ∧ inverse p q r s * basis p q r s = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [basis, inverse, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> nlinarith

theorem basis_height (p q r s : ℤ) (H : ℕ) (hp : |p| ≤ (H : ℤ)) (hq : |q| ≤ (H : ℤ))
    (hr : |r| ≤ (H : ℤ) ^ 2 + 1) (hs : |s| ≤ (H : ℤ) ^ 2 + 1) :
    (∀ i j, |basis p q r s i j| ≤ ((H ^ 2 + H + 1 : ℕ) : ℤ)) ∧
      ∀ i j, |inverse p q r s i j| ≤ ((H ^ 2 + H + 1 : ℕ) : ℤ) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [basis, inverse] <;>
    nlinarith [sq_nonneg (H : ℤ), Nat.cast_nonneg (α := ℤ) H]

theorem exists_bounded_extension (z : Fin 2 → ℤ) (H : ℕ)
    (hz : (z 0).natAbs.Coprime (z 1).natAbs) (hH : ∀ i, |z i| ≤ (H : ℤ)) :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B = 1 ∧ B * A = 1 ∧
      (∀ i, A i 0 = z i) ∧
      (∀ i j, |A i j| ≤ ((H ^ 2 + H + 1 : ℕ) : ℤ)) ∧
      ∀ i j, |B i j| ≤ ((H ^ 2 + H + 1 : ℕ) : ℤ) := by
  obtain ⟨r, s, hbezout, hr, hs⟩ := bounded_bezout (z 0) (z 1) H
    ((UnimodularBinaryCoordinates.primitive_iff_isCoprime z).mp hz) (hH 0) (hH 1)
  obtain ⟨hAB, hBA⟩ := basis_inverse (z 0) (z 1) r s hbezout
  obtain ⟨hA, hB⟩ := basis_height (z 0) (z 1) r s H (hH 0) (hH 1) hr hs
  refine ⟨basis (z 0) (z 1) r s, inverse (z 0) (z 1) r s, hAB, hBA, ?_, hA, hB⟩
  intro i
  fin_cases i <;> rfl

end PaperP1.PrimitiveBinaryBasis
