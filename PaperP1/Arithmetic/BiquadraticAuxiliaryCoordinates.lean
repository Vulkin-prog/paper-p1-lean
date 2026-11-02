module

public import PaperP1.Arithmetic.BiquadraticAuxiliaryBudget
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Actual rectangular coefficient slots and triangular equations for the biquadratic auxiliary -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticAuxiliaryCoordinates

open Finset PaperP1.BiquadraticAuxiliaryBudget

abbrev CoefficientIndex (q : ℕ) (r s : Fin 3 → ℕ) :=
  (Fin (3 * q + 1) × Fin (3 * q + 1)) ⊕
    (Σ i : Fin 3, Fin (3 * q - r i + 1) × Fin (3 * q - s i + 1))

abbrev EquationIndex (q : ℕ) := Σ a : Fin (6 * q + 1), Fin (6 * q + 1 - a.val)

theorem coefficient_card (q : ℕ) (r s : Fin 3 → ℕ) :
    Fintype.card (CoefficientIndex q r s) = unknownCount q r s := by
  simp only [CoefficientIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_sigma, unknownCount, pow_two]

theorem triangular_sum (m : ℕ) : (∑ a ∈ range m, (m - a)) * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (∑ a ∈ range m, (m + 1 - a)) = (∑ a ∈ range m, (m - a)) + m := by
      calc
        _ = ∑ a ∈ range m, ((m - a) + 1) := sum_congr rfl fun a ha ↦ by have := mem_range.mp ha; omega
        _ = _ := by rw [sum_add_distrib]; simp only [sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_id]
    rw [sum_range_succ, hs]
    rw [show m + 1 - m = 1 by omega]
    nlinarith only [ih]

theorem equation_card (q : ℕ) : Fintype.card (EquationIndex q) = equationCount q := by
  simp only [EquationIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range]
  have h := triangular_sum (6 * q + 1)
  unfold equationCount
  rw [← Nat.mul_div_cancel (∑ a ∈ range (6 * q + 1), (6 * q + 1 - a)) Nat.zero_lt_two, h]

theorem equation_total_degree (q : ℕ) (a : EquationIndex q) : a.1.val + a.2.val ≤ 6 * q := by
  have hfirst := a.1.isLt
  have hsecond := a.2.isLt
  omega

def coefficientEquiv (q : ℕ) (r s : Fin 3 → ℕ) :
    CoefficientIndex q r s ≃ Fin (unknownCount q r s) := Fintype.equivFinOfCardEq (coefficient_card q r s)

def equationEquiv (q : ℕ) : EquationIndex q ≃ Fin (equationCount q) :=
  Fintype.equivFinOfCardEq (equation_card q)

theorem indexed_kernel (q : ℕ) (r s : Fin 3 → ℕ) (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (H : ℕ) (hH : 0 < H) (A : EquationIndex q → CoefficientIndex q r s → ℤ)
    (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ ((3 * unknownCount q r s * H) ^ 7 : ℕ)) ∧
        ∀ j, ∑ i, A j i * w i = 0 := by
  let ec := coefficientEquiv q r s
  let ee := equationEquiv q
  let A' := fun j : Fin (equationCount q) ↦ fun i : Fin (unknownCount q r s) ↦ A (ee.symm j) (ec.symm i)
  obtain ⟨w, hne, hbound, hzero⟩ := exists_kernel q r s hr hs H hH A' (fun j i ↦ hA _ _)
  refine ⟨fun i ↦ w (ec i), ?_, fun i ↦ hbound _, ?_⟩
  · intro hw
    apply hne
    funext i
    have h := congrFun hw (ec.symm i)
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h
  · intro j
    have hz : (∑ i : Fin (unknownCount q r s), A j (ec.symm i) * w i) = 0 := by
      simpa only [A', Equiv.symm_apply_apply] using hzero (ee j)
    calc
      _ = ∑ i : Fin (unknownCount q r s), A j (ec.symm i) * w i := by
        simpa only [Equiv.symm_apply_apply] using Equiv.sum_comp ec (fun i ↦ A j (ec.symm i) * w i)
      _ = 0 := hz

end PaperP1.BiquadraticAuxiliaryCoordinates
