module

public import PaperP1.Probability.IteratedPoissonDifferences
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact norms from finite negative supports and second-difference telescoping -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteNegativeMass

open Finset PaperP1.PoissonSequence PaperP1.IteratedPoissonDifferences

def extended (a : ℕ → ℝ) (k : ℤ) : ℝ := if 0 ≤ k then a k.toNat else 0

theorem extended_nat (a : ℕ → ℝ) (k : ℕ) : extended a k = a k := by simp [extended]

theorem shift_eq_extended (a : ℕ → ℝ) (k : ℕ) :
    shift a k = extended a ((k : ℤ) - 1) := by
  cases k with
  | zero => simp [extended]
  | succ k =>
    have h : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
    rw [h, extended_nat, shift_succ]

theorem second_shift_eq_extended (a : ℕ → ℝ) (k : ℕ) :
    shift (shift a) k = extended a ((k : ℤ) - 2) := by
  cases k with
  | zero => simp [extended]
  | succ k =>
    cases k with
    | zero => simp [extended]
    | succ k =>
      have h : ((k + 1 + 1 : ℕ) : ℤ) - 2 = (k : ℤ) := by omega
      rw [h, extended_nat, shift_succ, shift_succ]

theorem l1_ge_twice_point (a : ℕ → ℝ) (ha : HasSum a 0) (j : ℕ) : 2 * a j ≤ l1 a := by
  let d : ℕ → ℝ := fun k ↦ if k = j then a j else 0
  have hd : HasSum d (a j) := by
    have h : HasSum d (∑ k ∈ ({j} : Finset ℕ), d k) := hasSum_sum_of_ne_finset_zero
      (fun k hk ↦ by
        have hkj : k ≠ j := by simpa only [mem_singleton] using hk
        simp only [d, ite_eq_right hkj])
    simpa only [sum_singleton, d, ite_true] using h
  have hm := (hd.mul_left 2).sub ha
  have hpoint (k : ℕ) : 2 * d k - a k ≤ |a k| := by
    by_cases hk : k = j
    · subst k
      simp only [d, ite_true]
      linarith [le_abs_self (a j)]
    · simp only [d, ite_eq_right hk, mul_zero, zero_sub]
      exact neg_le_abs (a k)
  have h := hm.summable.tsum_le_tsum hpoint ha.summable.abs
  rw [hm.tsum_eq] at h
  simpa only [sub_zero, l1] using h

theorem l1_eq_negative_sum (a : ℕ → ℝ) (ha : HasSum a 0) (S : Finset ℕ)
    (hneg : ∀ k, a k < 0 ↔ k ∈ S) : l1 a = -2 * ∑ k ∈ S, a k := by
  let f : ℕ → ℝ := fun k ↦ if k ∈ S then a k else 0
  have hf : HasSum f (∑ k ∈ S, a k) := by
    have h : HasSum f (∑ k ∈ S, f k) := hasSum_sum_of_ne_finset_zero
      (fun k hk ↦ by simp only [f, ite_eq_right_iff]; exact fun h ↦ False.elim (hk h))
    convert h using 1
    apply sum_congr rfl
    intro k hk
    simp only [f, ite_eq_left hk]
  have hid : (fun k : ℕ ↦ |a k|) = (fun k ↦ a k - 2 * f k) := by
    funext k
    by_cases hk : k ∈ S
    · have h := (hneg k).mpr hk
      simp only [f, ite_eq_left hk, abs_of_neg h]
      ring
    · have h : 0 ≤ a k := le_of_not_gt (fun h ↦ hk ((hneg k).mp h))
      simp only [f, ite_eq_right hk, mul_zero, sub_zero, abs_of_nonneg h]
  have h := ha.sub (hf.mul_left 2)
  rw [show (0 : ℝ) - 2 * (∑ k ∈ S, a k) = -2 * ∑ k ∈ S, a k by ring] at h
  unfold l1
  rw [hid]
  exact h.tsum_eq

theorem secondDifference_interval_sum (a : ℕ → ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    (∑ k ∈ Icc i j, secondDifference a k) =
      a j - shift a j - shift a i + shift (shift a) i := by
  let d : ℕ → ℝ := fun k ↦ a k - shift a k
  have hpoint (k : ℕ) (hk : 1 ≤ k) : secondDifference a k = d k - d (k - 1) := by
    cases k with
    | zero => omega
    | succ k => simp only [secondDifference, d, shift_succ, Nat.add_sub_cancel]; ring
  have heq : (∑ k ∈ Icc i j, secondDifference a k) = ∑ k ∈ Icc i j, (d k - d (k - 1)) :=
    sum_congr rfl (fun k hk ↦ hpoint k (hi.trans (mem_Icc.mp hk).1))
  have hsum : (∑ k ∈ Icc i j, (d k - d (k - 1))) = d j - d (i - 1) := by
    simpa only [Nat.add_sub_cancel] using sum_Icc_sub hij (fun k ↦ d (k - 1))
  have hiend : d (i - 1) = shift a i - shift (shift a) i := by
    cases i with
    | zero => omega
    | succ i => simp only [d, Nat.add_sub_cancel, shift_succ]
  rw [heq, hsum, hiend]
  dsimp [d]
  ring

end PaperP1.FiniteNegativeMass
