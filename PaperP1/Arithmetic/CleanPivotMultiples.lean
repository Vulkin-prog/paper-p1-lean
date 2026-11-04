module

public import PaperP1.Combinatorics.IntervalMultiples
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-! # Exact lower and collision upper counts before clean forcing pairs

Intervals use `(A,A+N]`, so every integer is positive and the bounds are
uniform in the position. The two-prime bound uses differences of solutions;
it does not assume a CRT density estimate or existence of a residue class.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CleanPivotMultiples

open Finset

def multiples (A N p : ℕ) : Finset ℕ := (Ioc A (A + N)).filter fun n ↦ p ∣ n

theorem prefix_card (X p : ℕ) : (multiples 0 X p).card = X / p := by
  simpa only [multiples, zero_add] using Nat.Ioc_filter_dvd_card_eq_div X p

theorem prefix_partition (A N p : ℕ) :
    multiples 0 (A + N) p = multiples 0 A p ∪ multiples A N p := by
  ext n
  simp only [multiples, zero_add, mem_union, mem_filter, mem_Ioc]
  omega

theorem partition_disjoint (A N p : ℕ) : Disjoint (multiples 0 A p) (multiples A N p) := by
  apply disjoint_left.mpr
  intro n hn hm
  have hna := (mem_Ioc.mp (mem_filter.mp hn).1).2
  have hma := (mem_Ioc.mp (mem_filter.mp hm).1).1
  omega

theorem card_add_prefix (A N p : ℕ) : A / p + (multiples A N p).card = (A + N) / p := by
  rw [← prefix_card A p, ← prefix_card (A + N) p, prefix_partition,
    card_union_of_disjoint (partition_disjoint A N p)]

theorem card_lower (A N p : ℕ) : N / p ≤ (multiples A N p).card := by
  have h := Nat.div_add_div_le_add_div (x := A) (y := N) (z := p)
  have he := card_add_prefix A N p
  omega

theorem card_upper (A N p : ℕ) : (multiples A N p).card ≤ N / p + 1 := by
  have he : Ioc A (A + N) = Ico (A + 1) (A + 1 + N) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [multiples, he]
  exact PaperP1.IntervalMultiples.card_multiples_interval_le (A + 1) N p

theorem real_bounds (A N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((multiples A N p).card : ℝ) ∧
      ((multiples A N p).card : ℝ) ≤ (N : ℝ) / p + 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · have hm := Nat.mod_lt N hp
    have hd := Nat.mod_add_div N p
    have hn : N < (N / p + 1) * p := by nlinarith only [hm, hd]
    have hnR : (N : ℝ) < ((N / p : ℕ) + 1 : ℝ) * p := by exact_mod_cast hn
    have hdiv : (N : ℝ) / p < ((N / p : ℕ) : ℝ) + 1 := (div_lt_iff₀ hpR).mpr hnR
    have hc : ((N / p : ℕ) : ℝ) ≤ (multiples A N p).card := by exact_mod_cast card_lower A N p
    linarith only [hdiv, hc]
  · have hc : ((multiples A N p).card : ℝ) ≤ ((N / p : ℕ) : ℝ) + 1 := by
      exact_mod_cast card_upper A N p
    have hdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    linarith only [hc, hdiv]

def crossHits (A N q r k : ℕ) : Finset ℕ :=
  (Ioc A (A + N)).filter fun n ↦ q ∣ n ∧ r ∣ n + k

theorem cross_card_upper (A N q r k : ℕ) (hqr : q.Coprime r) :
    (crossHits A N q r k).card ≤ N / (q * r) + 1 := by
  let S := crossHits A N q r k
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := S.min'_mem hS
    have hma : A < m := (mem_Ioc.mp (mem_filter.mp hm).1).1
    have hmq : q ∣ m := (mem_filter.mp hm).2.1
    have hmr : r ∣ m + k := (mem_filter.mp hm).2.2
    have hlow (n : ℕ) (hn : n ∈ S) : m ≤ n := S.min'_le n hn
    have hdiv (n : ℕ) (hn : n ∈ S) : q * r ∣ n - m := by
      have hnq : q ∣ n - m := Nat.dvd_sub (mem_filter.mp hn).2.1 hmq
      have hnr : r ∣ n - m := by
        simpa only [Nat.add_sub_add_right] using Nat.dvd_sub (mem_filter.mp hn).2.2 hmr
      exact hqr.mul_dvd_of_dvd_of_dvd hnq hnr
    have hc : S.card ≤ (range (N / (q * r) + 1)).card := by
      apply card_le_card_of_injOn (fun n ↦ (n - m) / (q * r))
      · intro n hn
        have hnN := (mem_Ioc.mp (mem_filter.mp hn).1).2
        have hnm : n - m ≤ N := by omega
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnm))
      · intro n hn l hl he
        change (n - m) / (q * r) = (l - m) / (q * r) at he
        have hnrec := Nat.div_mul_cancel (hdiv n hn)
        have hlrec := Nat.div_mul_cancel (hdiv l hl)
        rw [he] at hnrec
        have hnlow := hlow n hn
        have hllow := hlow l hl
        omega
    simpa only [card_range] using hc
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ _
    rw [he, card_empty]
    exact Nat.zero_le _

theorem cross_real_upper (A N q r k : ℕ) (hqr : q.Coprime r) :
    ((crossHits A N q r k).card : ℝ) ≤ (N : ℝ) / ((q : ℝ) * r) + 1 := by
  have hc : ((crossHits A N q r k).card : ℝ) ≤ ((N / (q * r) : ℕ) : ℝ) + 1 := by
    exact_mod_cast cross_card_upper A N q r k hqr
  have hd : ((N / (q * r) : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * r) := by
    simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := N) (n := q * r))
  linarith only [hc, hd]

end PaperP1.CleanPivotMultiples
