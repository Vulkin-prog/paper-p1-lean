module

public import PaperP1.Arithmetic.LogarithmicPrimeCover

/-! # Redundant actual prime covers for averaging point counts

A pool of twice the obstruction budget supplies at least that many good primes
for every nonzero obstruction. This retains multiplicity instead of choosing one.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RedundantPrimeCover

open Finset

theorem avoiding_card (P m : ℕ) (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime ∧ P ≤ p) (n : ℤ) (hne : n ≠ 0)
    (hsmall : n.natAbs < P ^ m) :
    T.card - m ≤ (T.filter (fun p : ℕ ↦ ¬(p : ℤ) ∣ n)).card := by
  classical
  let B := T.filter (fun p : ℕ ↦ (p : ℤ) ∣ n)
  have hbad : B.card < m := by
    by_contra hh
    have hmany : m ≤ B.card := by omega
    obtain ⟨V, hV, hcard⟩ := exists_subset_card_eq hmany
    have hprod : P ^ m ≤ ∏ p ∈ V, p := by
      calc
        _ = ∏ _p ∈ V, P := by simp only [prod_const, hcard]
        _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _)
          (fun p hp ↦ (hprime p (mem_filter.mp (hV hp)).1).2)
    obtain ⟨p, hp, hnot⟩ := DyadicPrimeCover.exists_nondividing V
      (fun p hp ↦ (hprime p (mem_filter.mp (hV hp)).1).1) n hne (hsmall.trans_le hprod)
    exact hnot (mem_filter.mp (hV hp)).2
  have hpartition := card_filter_add_card_filter_not (s := T) (fun p : ℕ ↦ (p : ℤ) ∣ n)
  change B.card + (T.filter (fun p : ℕ ↦ ¬(p : ℤ) ∣ n)).card = T.card at hpartition
  omega

theorem uniform_pool : ∃ P₀ : ℕ, 16 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ m : ℕ,
    (m : ℝ) * Real.log P ≤ P →
    ∃ T : Finset ℕ, T.card = 2 * m ∧ (∀ p ∈ T, p.Prime ∧ P < p ∧ p ≤ 16 * P) ∧
      (∑ p ∈ T, p) ≤ 32 * m * P ∧
      ∀ n : ℤ, n ≠ 0 → n.natAbs < P ^ m →
        m ≤ (T.filter (fun p : ℕ ↦ ¬(p : ℤ) ∣ n)).card := by
  classical
  obtain ⟨P₀, hP₀, hpool⟩ := LogarithmicPrimeCover.uniform_pool
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP m hm
  have hdouble : ((2 * m : ℕ) : ℝ) * Real.log P ≤ 2 * P := by
    push_cast
    nlinarith only [hm]
  obtain ⟨T, hcard, hprime, hsum, _havoid⟩ := hpool P hP (2 * m) hdouble
  refine ⟨T, hcard, hprime, by nlinarith only [hsum], ?_⟩
  intro n hn hsmall
  have hh := avoiding_card P m T (fun p hp ↦ ⟨(hprime p hp).1, (hprime p hp).2.1.le⟩) n hn hsmall
  rw [hcard] at hh
  omega

end PaperP1.RedundantPrimeCover
