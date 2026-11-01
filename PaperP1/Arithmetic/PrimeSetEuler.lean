module

public import PaperP1.Arithmetic.SmoothSquarefreeCount
public import PaperP1.Analysis.ReciprocalSqrtSum
public import Mathlib.Data.Finset.Max

/-! # A finite prime-set Euler bound with its literal cardinality constant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeSetEuler

open Finset PaperP1.SmoothSquarefreeCount

theorem sum_neg_half_le (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    (∑ p ∈ P, (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 2 * Real.sqrt P.card := by
  classical
  revert hP
  refine Finset.strongInductionOn P ?_
  intro P ih hP
  by_cases hPempty : P = ∅
  · subst P
    simp
  · let p := P.max' (nonempty_iff_ne_empty.mpr hPempty)
    have hp : p ∈ P := max'_mem _ _
    have hsub : P ⊆ Icc 1 p := fun q hq ↦ mem_Icc.mpr ⟨hP q hq, P.le_max' q hq⟩
    have hcard : P.card ≤ p := by simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
    have hcardpos : 0 < P.card := card_pos.mpr ⟨p, hp⟩
    have hcardR : (0 : ℝ) < P.card := by exact_mod_cast hcardpos
    have herase := ih (P.erase p) (erase_ssubset hp) (fun q hq ↦ hP q (mem_of_mem_erase hq))
    rw [card_erase_of_mem hp] at herase
    have hterm := Real.rpow_le_rpow_of_nonpos hcardR (by exact_mod_cast hcard : (P.card : ℝ) ≤ p)
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have hdiff := PaperP1.inv_sqrt_nat_le_two_mul_sqrt_sub P.card (by omega)
    rw [← PaperP1.rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg P.card)] at hdiff
    have hsum := sum_erase_add P (fun q : ℕ ↦ (q : ℝ) ^ (-(1 / 2 : ℝ))) hp
    linarith

theorem euler_half_le (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    eulerProduct P (1 / 2) ≤ Real.exp (2 * Real.sqrt P.card) := by
  calc
    _ ≤ Real.exp (∑ p ∈ P, (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
      Real.prod_one_add_le_exp_sum _ (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ _ := Real.exp_le_exp.mpr (sum_neg_half_le P hP)

theorem naturalValues_card_le_sqrt_exp (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (X : ℕ) :
    ((naturalValues P X).card : ℝ) ≤ Real.sqrt X * Real.exp (2 * Real.sqrt P.card) := by
  have h := card_naturalValues_le_euler P hP X (1 / 2) le_rfl
  rw [← Real.sqrt_eq_rpow] at h
  exact h.trans (mul_le_mul_of_nonneg_left (euler_half_le P hP) (Real.sqrt_nonneg X))

end PaperP1.PrimeSetEuler
