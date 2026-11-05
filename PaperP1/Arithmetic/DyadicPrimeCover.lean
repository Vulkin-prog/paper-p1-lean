module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Int.Basic

/-! # A fixed finite dyadic prime family avoids every sufficiently small nonzero integer -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPrimeCover

open Finset

theorem exists_pool (P m : ℕ) (hP : 0 < P) :
    ∃ T : Finset ℕ, T.card = m ∧ (∀ p ∈ T, p.Prime ∧ P < p ∧ p ≤ 2 ^ m * P) ∧
      P ^ m ≤ ∏ p ∈ T, p := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp⟩
  | succ m ih =>
    obtain ⟨T, hcard, hprime, hprod⟩ := ih
    obtain ⟨q, hq, hlow, hupp⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ m * P) (by positivity)
    have hone : 1 ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hbase : P ≤ 2 ^ m * P := by nlinarith
    have hstep : 2 ^ m * P ≤ 2 ^ (m + 1) * P := by rw [pow_succ]; nlinarith
    have hnot : q ∉ T := fun h ↦ (not_lt_of_ge (hprime q h).2.2) hlow
    refine ⟨insert q T, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem hnot, hcard]
    · intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · refine ⟨hq, hbase.trans_lt hlow, ?_⟩
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hupp
      · exact ⟨(hprime p hp).1, (hprime p hp).2.1, (hprime p hp).2.2.trans hstep⟩
    · rw [prod_insert hnot, pow_succ]
      have hqP : P ≤ q := (hbase.trans_lt hlow).le
      calc
        P ^ m * P ≤ (∏ p ∈ T, p) * q := Nat.mul_le_mul hprod hqP
        _ = _ := by rw [Nat.mul_comm]

theorem pool_sum_bound (P m : ℕ) (T : Finset ℕ) (hcard : T.card = m)
    (hupper : ∀ p ∈ T, p ≤ 2 ^ m * P) :
    (∑ p ∈ T, p) ≤ m * 2 ^ m * P := by
  calc
    _ ≤ ∑ _p ∈ T, 2 ^ m * P := Finset.sum_le_sum hupper
    _ = _ := by simp only [sum_const, smul_eq_mul, hcard]; ring

theorem exists_nondividing (T : Finset ℕ) (hprime : ∀ p ∈ T, p.Prime) (n : ℤ)
    (hne : n ≠ 0) (hsmall : n.natAbs < ∏ p ∈ T, p) :
    ∃ p ∈ T, ¬(p : ℤ) ∣ n := by
  classical
  by_contra h
  have hall : ∀ p ∈ T, (p : ℤ) ∣ n := by
    intro p hp
    by_contra hn
    exact h ⟨p, hp, hn⟩
  have hd : (∏ p ∈ T, p) ∣ n.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (hprime p hp).prime
    · intro p hp
      have ha := Int.natAbs_dvd_natAbs.mpr (hall p hp)
      simpa only [Int.natAbs_natCast] using ha
  have hn : 0 < n.natAbs := Int.natAbs_pos.mpr hne
  exact (not_lt_of_ge (Nat.le_of_dvd hn hd)) hsmall

theorem uniform_pool (P m : ℕ) (hP : 0 < P) :
    ∃ T : Finset ℕ, T.card = m ∧ (∀ p ∈ T, p.Prime ∧ P < p ∧ p ≤ 2 ^ m * P) ∧
      (∑ p ∈ T, p) ≤ m * 2 ^ m * P ∧
        ∀ n : ℤ, n ≠ 0 → n.natAbs < P ^ m → ∃ p ∈ T, ¬(p : ℤ) ∣ n := by
  obtain ⟨T, hcard, hprime, hprod⟩ := exists_pool P m hP
  refine ⟨T, hcard, hprime, pool_sum_bound P m T hcard (fun p hp ↦ (hprime p hp).2.2), ?_⟩
  intro n hn hsmall
  exact exists_nondividing T (fun p hp ↦ (hprime p hp).1) n hn (hsmall.trans_le hprod)

end PaperP1.DyadicPrimeCover
