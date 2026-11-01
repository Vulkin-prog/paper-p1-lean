module

public import PaperP1.Asymptotics.FactorialLogBounds
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity

/-! # A finite factorial lower bound for actual distinct prime products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeFactorialBudget

open Finset

theorem positive_factorial_le_prod (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    S.card.factorial ≤ ∏ n ∈ S, n := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha : a ∉ S := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have hsub : insert a S ⊆ Icc 1 a := by
      intro n hn
      obtain hna | hnS := mem_insert.mp hn
      · subst n
        exact mem_Icc.mpr ⟨hS a (mem_insert_self a S), le_rfl⟩
      · exact mem_Icc.mpr ⟨hS n (mem_insert_of_mem hnS), (hmax n hnS).le⟩
    have hc : S.card + 1 ≤ a := by
      have ht := card_le_card hsub
      simpa only [card_insert_of_notMem ha, Nat.card_Icc, Nat.add_sub_cancel] using ht
    have hi := ih (fun n hn ↦ hS n (mem_insert_of_mem hn))
    rw [card_insert_of_notMem ha, Nat.factorial_succ, prod_insert ha]
    exact Nat.mul_le_mul hc hi

theorem prime_factorial_le (n : ℕ) (hn : 0 < n) : n.primeFactors.card.factorial ≤ n := by
  calc
    _ ≤ ∏ p ∈ n.primeFactors, p := positive_factorial_le_prod _
      (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos)
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem prime_card_log_lower (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card : ℝ) * (Real.log n.primeFactors.card - 1) ≤ Real.log n := by
  by_cases hm : n.primeFactors.card = 0
  · simp only [hm, Nat.cast_zero, zero_mul]
    exact Real.log_nonneg (by exact_mod_cast hn)
  · have hfac := (PaperP1.FactorialLogBounds.log_factorial_bounds n.primeFactors.card (by omega)).1
    have hle : (n.primeFactors.card.factorial : ℝ) ≤ n := by exact_mod_cast prime_factorial_le n hn
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n.primeFactors.card.factorial) hle
    nlinarith

theorem prime_card_lt_of_log_budget (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (hlogt : 1 ≤ Real.log t) (hbudget : Real.log n < t * (Real.log t - 1)) :
    (n.primeFactors.card : ℝ) < t := by
  by_contra hnot
  have hm : t ≤ (n.primeFactors.card : ℝ) := le_of_not_gt hnot
  have hlog := Real.log_le_log ht hm
  have hprod : t * (Real.log t - 1) ≤
      (n.primeFactors.card : ℝ) * (Real.log n.primeFactors.card - 1) :=
    mul_le_mul hm (by linarith) (by linarith) (Nat.cast_nonneg _)
  have hlower := prime_card_log_lower n hn
  linarith

theorem squarefree_divisors_card (n : ℕ) (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  calc
    _ = ∏ _p ∈ n.primeFactors, 2 := by
      apply prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp

end PaperP1.PrimeFactorialBudget
