module

public import PaperP1.Arithmetic.PrimeSubsetAllocations
public import Mathlib.Data.Nat.Factors
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-! # Indexed first-passage products and smooth-factor crossings from a prescribed base -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProductFirstPassage

open Finset

theorem indexed_crossing {ι : Type*} (S : Finset ι) (f : ι → ℕ) (X Y : ℝ) (hX : 1 ≤ X)
    (hf : ∀ i ∈ S, 1 ≤ f i ∧ (f i : ℝ) ≤ Y) (hprod : X < (S.prod f : ℕ)) :
    ∃ T : Finset ι, T ⊆ S ∧ X < (T.prod f : ℕ) ∧ (T.prod f : ℕ) ≤ X * Y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty, Nat.cast_one] at hprod; linarith
  | @insert i S hi ih =>
    by_cases hrest : X < (S.prod f : ℕ)
    · obtain ⟨T, hT, hlo, hhi⟩ := ih (fun j hj ↦ hf j (mem_insert_of_mem hj)) hrest
      exact ⟨T, hT.trans (subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert i S, Subset.rfl, hprod, ?_⟩
      rw [prod_insert hi, Nat.cast_mul]
      have hY : 0 ≤ Y := (Nat.cast_nonneg (f i)).trans (hf i (mem_insert_self _ _)).2
      exact (mul_le_mul (hf i (mem_insert_self _ _)).2 (le_of_not_gt hrest)
        (Nat.cast_nonneg _) hY).trans_eq (mul_comm _ _)

theorem list_crossing (P : List ℕ) (a : ℕ) (X Y : ℝ) (ha : 0 < a)
    (haX : (a : ℝ) ≤ X)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ Y) (hbig : X < ((a * P.prod : ℕ) : ℝ)) :
    ∃ Q : List ℕ, Q.Sublist P ∧ X < ((a * Q.prod : ℕ) : ℝ) ∧
      ((a * Q.prod : ℕ) : ℝ) ≤ X * Y := by
  induction P generalizing a with
  | nil => simp only [List.prod_nil, mul_one] at hbig; linarith
  | cons p P ih =>
    have hp := hP p List.mem_cons_self
    have haP : 0 < a * p := Nat.mul_pos ha (by omega)
    by_cases hcross : X < ((a * p : ℕ) : ℝ)
    · refine ⟨[p], by simp, by simpa only [List.prod_singleton] using hcross, ?_⟩
      simp only [List.prod_singleton, Nat.cast_mul]
      exact mul_le_mul haX hp.2 (Nat.cast_nonneg _) ((Nat.cast_nonneg a).trans haX)
    · have hrest : X < (((a * p) * P.prod : ℕ) : ℝ) := by
        simpa only [List.prod_cons, Nat.mul_assoc] using hbig
      obtain ⟨Q, hQ, hlo, hhi⟩ := ih (a * p) haP (le_of_not_gt hcross) (fun q hq ↦ hP q (List.mem_cons_of_mem p hq)) hrest
      exact ⟨p :: Q, hQ.cons_cons p,
        by simpa only [List.prod_cons, Nat.mul_assoc] using hlo,
        by simpa only [List.prod_cons, Nat.mul_assoc] using hhi⟩

theorem smooth_crossing (s a Y : ℕ) (X : ℝ) (hs : 0 < s) (ha : 0 < a)
    (haX : (a : ℝ) ≤ X)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ s → p ≤ Y)
    (hbig : X < ((a * s : ℕ) : ℝ)) :
    ∃ d : ℕ, 0 < d ∧ d ∣ s ∧ X < ((a * d : ℕ) : ℝ) ∧
      ((a * d : ℕ) : ℝ) ≤ X * Y := by
  have hlist : ∀ p ∈ s.primeFactorsList, 1 ≤ p ∧ (p : ℝ) ≤ Y := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    exact ⟨hprime.one_lt.le, by exact_mod_cast hsmooth p hprime (Nat.dvd_of_mem_primeFactorsList hp)⟩
  have hprod : s.primeFactorsList.prod = s := Nat.prod_primeFactorsList hs.ne'
  obtain ⟨Q, hQ, hlo, hhi⟩ := list_crossing s.primeFactorsList a X Y ha haX hlist
    (by simpa only [hprod] using hbig)
  have hd : Q.prod ∣ s := by
    rw [← hprod]
    exact hQ.prod_dvd_prod
  have hdp : 0 < Q.prod := Nat.pos_of_dvd_of_pos hd hs
  exact ⟨Q.prod, hdp, hd, hlo, hhi⟩

end PaperP1.ProductFirstPassage
