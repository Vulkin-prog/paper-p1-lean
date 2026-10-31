module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-! # Multiples in a translated interval, uniformly in its position -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntervalMultiples

open Finset

theorem card_multiples_interval_le (U B p : ℕ) :
    ((Ico U (U + B)).filter fun n ↦ p ∣ n).card ≤ B / p + 1 := by
  let S := (Ico U (U + B)).filter fun n ↦ p ∣ n
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := S.min'_mem hS
    have hmU : U ≤ m := (mem_Ico.mp (mem_filter.mp hm).1).1
    have hmp : p ∣ m := (mem_filter.mp hm).2
    have hlow (n : ℕ) (hn : n ∈ S) : m ≤ n := S.min'_le n hn
    have hdiv (n : ℕ) (hn : n ∈ S) : p ∣ n - m :=
      Nat.dvd_sub (mem_filter.mp hn).2 hmp
    have hcard : S.card ≤ (range (B / p + 1)).card := by
      apply card_le_card_of_injOn (fun n ↦ (n - m) / p)
      · intro n hn
        have hnB := (mem_Ico.mp (mem_filter.mp hn).1).2
        have hnm : n - m ≤ B := by omega
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnm))
      · intro n hn k hk heq
        change (n - m) / p = (k - m) / p at heq
        have hnrec := Nat.div_mul_cancel (hdiv n hn)
        have hkrec := Nat.div_mul_cancel (hdiv k hk)
        rw [heq] at hnrec
        have hnlow := hlow n hn
        have hklow := hlow k hk
        omega
    simpa only [card_range] using hcard
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ _
    rw [he, card_empty]
    exact Nat.zero_le _

end PaperP1.IntervalMultiples
