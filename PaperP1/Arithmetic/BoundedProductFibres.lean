module

public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Arithmetic.OddPrimePivot
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Associated

/-! # Bounded integer products have divisor-controlled fibres

No distribution of primes or smooth-number asymptotic is used. The exact
product map on a finite Cartesian power retains every factorization.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedProductFibres

open Finset PaperP1.OddPrimePivot

def tuples (k : ℕ) (I : Finset ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ ↦ I)

def value {k : ℕ} (x : Fin k → ℕ) : ℕ := ∏ i, x i

theorem tuples_card (k : ℕ) (I : Finset ℕ) : (tuples k I).card = I.card ^ k :=
  Fintype.card_piFinset_const I k

theorem fibre_card (k : ℕ) (I : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    ((tuples k I).filter (fun x ↦ value x = n)).card ≤ n.divisors.card ^ k := by
  classical
  have hsub : (tuples k I).filter (fun x ↦ value x = n) ⊆ tuples k n.divisors := by
    intro x hx
    have heq := (mem_filter.mp hx).2
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn.ne'⟩
    rw [← heq]
    exact dvd_prod_of_mem _ (mem_univ i)
  exact (card_le_card hsub).trans_eq (tuples_card k n.divisors)

theorem image_card (k : ℕ) (I : Finset ℕ) (hI : ∀ a ∈ I, 0 < a)
    (M : ℝ) (hdiv : ∀ n ∈ (tuples k I).image value, (n.divisors.card : ℝ) ^ k ≤ M) :
    (I.card : ℝ) ^ k ≤ (((tuples k I).image value).card : ℝ) * M := by
  classical
  have hfibre (n : ℕ) (hn : n ∈ (tuples k I).image value) :
      (((tuples k I).filter (fun x ↦ value x = n)).card : ℝ) ≤ M := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    have hpos : 0 < value x := prod_pos (fun i _ ↦ hI _ (Fintype.mem_piFinset.mp hx i))
    have hh : (((tuples k I).filter (fun y ↦ value y = value x)).card : ℝ) ≤
        ((value x).divisors.card : ℝ) ^ k := by exact_mod_cast fibre_card k I (value x) hpos
    exact hh.trans (hdiv _ (mem_image.mpr ⟨x, hx, rfl⟩))
  calc
    _ = ((tuples k I).card : ℝ) := by rw [tuples_card, Nat.cast_pow]
    _ = ∑ n ∈ (tuples k I).image value, (((tuples k I).filter (fun x ↦ value x = n)).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image value (tuples k I)
    _ ≤ ∑ _n ∈ (tuples k I).image value, M := sum_le_sum hfibre
    _ = _ := by simp

theorem largest_prime_bound (k Y : ℕ) (hY : 1 ≤ Y) (x : Fin k → ℕ)
    (hpos : ∀ i, 0 < x i) (hupper : ∀ i, x i ≤ Y) : largestPrimeFactor (value x) ≤ Y := by
  apply max_le hY
  apply Finset.sup_le
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd : p ∣ value x := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨i, _hi, hpi⟩ := hprime.prime.exists_mem_finset_dvd hd
  exact (Nat.le_of_dvd (hpos i) hpi).trans (hupper i)

theorem reciprocal_lower (k Y : ℕ) (I : Finset ℕ) (hY : 1 ≤ Y)
    (hI : ∀ a ∈ I, 0 < a ∧ a ≤ Y) (M : ℝ) (hM : 0 ≤ M)
    (hdiv : ∀ n ∈ (tuples k I).image value, (n.divisors.card : ℝ) ^ k ≤ M) :
    (I.card : ℝ) ^ k ≤ M * Y *
      (∑ n ∈ (tuples k I).image value, 1 / (largestOddPrime n : ℝ)) := by
  have hcount := image_card k I (fun a ha ↦ (hI a ha).1) M hdiv
  have hpoint (n : ℕ) (hn : n ∈ (tuples k I).image value) :
      (1 : ℝ) ≤ Y * (1 / (largestOddPrime n : ℝ)) := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    have hbound := (largestOddPrime_le_largestPrimeFactor (value x)).trans
      (largest_prime_bound k Y hY x (fun i ↦ (hI _ (Fintype.mem_piFinset.mp hx i)).1)
        (fun i ↦ (hI _ (Fintype.mem_piFinset.mp hx i)).2))
    have hp : (0 : ℝ) < largestOddPrime (value x) := by exact_mod_cast largestOddPrime_pos (value x)
    have hh : (largestOddPrime (value x) : ℝ) ≤ Y := by exact_mod_cast hbound
    rw [show (Y : ℝ) * (1 / (largestOddPrime (value x) : ℝ)) = (Y : ℝ) / largestOddPrime (value x) by ring]
    exact (le_div_iff₀ hp).mpr (by simpa only [one_mul] using hh)
  have hsum := sum_le_sum hpoint
  simp only [sum_const, nsmul_eq_mul, mul_one, ← mul_sum] at hsum
  calc
    _ ≤ (((tuples k I).image value).card : ℝ) * M := hcount
    _ ≤ (Y * (∑ n ∈ (tuples k I).image value, 1 / (largestOddPrime n : ℝ))) * M :=
      mul_le_mul_of_nonneg_right hsum hM
    _ = _ := by ring

end PaperP1.BoundedProductFibres
