module

public import PaperP1.Algebra.SmallIntegerKernel
public import Mathlib.Algebra.BigOperators.Fin

/-! # The exact coefficient and equation budgets in the two-witness biquadratic construction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticAuxiliaryBudget

open Finset

def unknownCount (q : ℕ) (r s : Fin 3 → ℕ) : ℕ :=
  (3 * q + 1) ^ 2 + ∑ i : Fin 3, (3 * q - r i + 1) * (3 * q - s i + 1)

def equationCount (q : ℕ) : ℕ := (6 * q + 1) * (6 * q + 2) / 2

theorem unknown_lower (q : ℕ) (r s : Fin 3 → ℕ) (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q) :
    21 * q ^ 2 + 18 * q + 4 ≤ unknownCount q r s := by
  have hterm : ∀ i, (2 * q + 1) ^ 2 ≤ (3 * q - r i + 1) * (3 * q - s i + 1) := by
    intro i
    rw [pow_two]
    exact Nat.mul_le_mul (by have := hr i; omega) (by have := hs i; omega)
  have hsum := sum_le_sum (fun i (_hi : i ∈ (univ : Finset (Fin 3))) ↦ hterm i)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold unknownCount
  have he : (3 * q + 1) ^ 2 + 3 * (2 * q + 1) ^ 2 = 21 * q ^ 2 + 18 * q + 4 := by ring
  omega

theorem unknown_upper (q : ℕ) (r s : Fin 3 → ℕ) :
    unknownCount q r s ≤ 4 * (3 * q + 1) ^ 2 := by
  have hterm : ∀ i, (3 * q - r i + 1) * (3 * q - s i + 1) ≤ (3 * q + 1) ^ 2 := by
    intro i
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hsum := sum_le_sum (fun i (_hi : i ∈ (univ : Finset (Fin 3))) ↦ hterm i)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold unknownCount
  omega

theorem equation_formula (q : ℕ) : equationCount q = 18 * q ^ 2 + 9 * q + 1 := by
  unfold equationCount
  rw [show (6 * q + 1) * (6 * q + 2) = (18 * q ^ 2 + 9 * q + 1) * 2 by ring, Nat.mul_div_cancel]
  omega

theorem sixfold_gap (q : ℕ) (r s : Fin 3 → ℕ) (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q) :
    7 * equationCount q < 6 * unknownCount q r s := by
  have h := unknown_lower q r s hr hs
  rw [equation_formula]
  nlinarith only [h, Nat.zero_le q]

theorem capacity_dimension (q : ℕ) (r s : Fin 3 → ℕ) (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q) :
    8 * equationCount q ≤ 7 * unknownCount q r s := by
  have h := sixfold_gap q r s hr hs
  omega

theorem exists_kernel (q : ℕ) (r s : Fin 3 → ℕ) (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (H : ℕ) (hH : 0 < H)
    (A : Fin (equationCount q) → Fin (unknownCount q r s) → ℤ)
    (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : Fin (unknownCount q r s) → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ ((3 * unknownCount q r s * H) ^ 7 : ℕ)) ∧
        ∀ j, ∑ i, A j i * w i = 0 := by
  have hpositive : 0 < unknownCount q r s := by
    have h := unknown_lower q r s hr hs
    omega
  exact SmallIntegerKernel.exists_small_kernel H hpositive hH (capacity_dimension q r s hr hs) A hA

theorem dimension_height (B q : ℕ) (hq : 1 ≤ q) (hB : q ≤ B) (r s : Fin 3 → ℕ) :
    3 * unknownCount q r s ≤ (B + 1) ^ (10 * q) := by
  have hupper := unknown_upper q r s
  have hqB : 3 * q + 1 ≤ 4 * B := by omega
  have hqBsq := Nat.pow_le_pow_left hqB 2
  have hfirst : 3 * unknownCount q r s ≤ 192 * B ^ 2 := by nlinarith only [hupper, hqBsq]
  have hconstant : 192 ≤ (B + 1) ^ 8 :=
    (by norm_num : 192 ≤ (2 : ℕ) ^ 8).trans (Nat.pow_le_pow_left (by omega : 2 ≤ B + 1) 8)
  calc
    _ ≤ 192 * B ^ 2 := hfirst
    _ ≤ (B + 1) ^ 8 * (B + 1) ^ 2 := Nat.mul_le_mul hconstant (Nat.pow_le_pow_left (Nat.le_succ B) 2)
    _ = (B + 1) ^ 10 := by rw [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < B + 1) (by omega)

theorem kernel_height (B q c H : ℕ) (hq : 1 ≤ q) (hB : q ≤ B) (r s : Fin 3 → ℕ)
    (hH : H ≤ (B + 1) ^ (c * q)) :
    (3 * unknownCount q r s * H) ^ 7 ≤ (B + 1) ^ ((7 * (10 + c)) * q) := by
  have hdim := dimension_height B q hq hB r s
  have hbase : 3 * unknownCount q r s * H ≤ (B + 1) ^ ((10 + c) * q) := by
    have h := Nat.mul_le_mul hdim hH
    rw [← pow_add, ← add_mul] at h
    exact h
  calc
    _ ≤ ((B + 1) ^ ((10 + c) * q)) ^ 7 := Nat.pow_le_pow_left hbase 7
    _ = _ := by rw [← pow_mul]; congr 1; ring

end PaperP1.BiquadraticAuxiliaryBudget
