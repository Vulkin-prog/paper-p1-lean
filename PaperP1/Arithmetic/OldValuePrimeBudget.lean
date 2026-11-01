module

public import PaperP1.Arithmetic.ConditionalWindowRank
public import PaperP1.Arithmetic.SmallPrimeBudget
public import PaperP1.Model.FiniteRademacher

/-! # The old raw windows give a uniform logarithmic prime-pool budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OldValuePrimeBudget

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ConditionalWindowRank

def rawValues (A : Finset ℕ) (L : ℕ) : Finset ℕ := A.biUnion fun x ↦ Ico (x - 1) (x + L)

def contactStarts (N L : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ ∃ y ∈ A, Nat.dist x y ≤ L

theorem rawValues_card_le (A : Finset ℕ) (L : ℕ) (hA : ∀ x ∈ A, 1 ≤ x) :
    (rawValues A L).card ≤ A.card * (L + 1) := by
  apply card_biUnion_le_card_mul
  intro x hx
  rw [Nat.card_Ico]
  have h := hA x hx
  omega

theorem rawValues_bounds {A : Finset ℕ} {N L : ℕ} (hA : A ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : L ≤ N) {n : ℕ} (hn : n ∈ rawValues A L) : 1 ≤ n ∧ n ≤ 3 * N := by
  obtain ⟨x, hx, hn⟩ := mem_biUnion.mp hn
  have hxb := mem_Ico.mp (hA hx)
  have hnb := mem_Ico.mp hn
  omega

theorem contactStarts_subset (N L : ℕ) (A : Finset ℕ) : contactStarts N L A ⊆ dyadicBlock N := filter_subset _ _

theorem log_sum_union_le (P Q : Finset ℕ) :
    (∑ p ∈ P ∪ Q, Real.log p) ≤ (∑ p ∈ P, Real.log p) + ∑ p ∈ Q, Real.log p := by
  have h := sum_union_inter (s₁ := P) (s₂ := Q) (f := fun p : ℕ ↦ Real.log p)
  have hnonneg : 0 ≤ ∑ p ∈ P ∩ Q, Real.log p := sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  linarith

theorem log_sum_biUnion_le (R : Finset ℕ) (S : ℕ → Finset ℕ) :
    (∑ p ∈ R.biUnion S, Real.log p) ≤ ∑ n ∈ R, ∑ p ∈ S n, Real.log p := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert n R hn ih =>
    rw [biUnion_insert, sum_insert hn]
    exact (log_sum_union_le (S n) (R.biUnion S)).trans (add_le_add le_rfl ih)

theorem primeFactors_log_sum_le {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ n.primeFactors, Real.log p) ≤ Real.log n := by
  have hprod : (0 : ℝ) < ((n.primeFactors.prod id : ℕ) : ℝ) := by
    exact_mod_cast prod_pos (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos)
  have hle : ((n.primeFactors.prod id : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hlog := Real.log_le_log hprod hle
  rw [Nat.cast_prod, Real.log_prod] at hlog
  · exact hlog
  · intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem oldPrimes_log_sum_le (R : Finset ℕ) (hR : ∀ n ∈ R, 0 < n) :
    (∑ p ∈ oldPrimes R, Real.log p) ≤ ∑ n ∈ R, Real.log n := by
  exact (log_sum_biUnion_le R Nat.primeFactors).trans
    (sum_le_sum fun n hn ↦ primeFactors_log_sum_le (hR n hn))

theorem primePool_log_sum_le (R : Finset ℕ) (B X : ℕ)
    (hR : ∀ n ∈ R, 1 ≤ n ∧ n ≤ X) :
    (∑ p ∈ primePool R B, Real.log p) ≤ (B : ℝ) * Real.log 4 + R.card * Real.log X := by
  have hold := oldPrimes_log_sum_le R (fun n hn ↦ by have h := (hR n hn).1; omega)
  have hvalues : (∑ n ∈ R, Real.log n) ≤ R.card * Real.log X := by
    calc
      _ ≤ ∑ _n ∈ R, Real.log X := sum_le_sum (fun n hn ↦
        Real.log_le_log (by exact_mod_cast (show 0 < n by have h := (hR n hn).1; omega))
          (by exact_mod_cast (hR n hn).2))
      _ = _ := by simp
  exact (log_sum_union_le _ _).trans (add_le_add (PaperP1.SmallPrimeBudget.prime_log_sum_le B)
    (hold.trans hvalues))

theorem raw_primePool_log_sum_le {A : Finset ℕ} {N L j : ℕ} (hA : A ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : L ≤ N) (hj : A.card ≤ j) :
    (∑ p ∈ primePool (rawValues A L) (L + 1), Real.log p) ≤
      ((L + 1 : ℕ) : ℝ) * Real.log 4 + (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) := by
  have h := primePool_log_sum_le (rawValues A L) (L + 1) (3 * N)
    (fun n hn ↦ rawValues_bounds hA hN hL hn)
  have hcard := (rawValues_card_le A L (fun x hx ↦ by have h := (mem_Ico.mp (hA hx)).1; omega)).trans
    (Nat.mul_le_mul_right (L + 1) hj)
  have hcardR : ((rawValues A L).card : ℝ) ≤ (j : ℝ) * (L + 1) := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardR (Real.log_natCast_nonneg (3 * N))
  linarith

end PaperP1.OldValuePrimeBudget
