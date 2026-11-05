module

public import PaperP1.Arithmetic.PolynomialPrimeCover
public import PaperP1.Arithmetic.ReciprocalOddPivots
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Exact squarefree prime-product populations and ordinary reciprocal lower bounds

A subset of actual primes is recovered from its integer product. The population
therefore pays no divisor multiplicity, including when its order varies.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeProductCensus

open Finset DefectCounting OddPrimePivot ReciprocalOddPivots

theorem product_injective (T : Finset ℕ) (hprime : ∀ p ∈ T, p.Prime)
    (U : Finset ℕ) (hU : U ⊆ T) (V : Finset ℕ) (hV : V ⊆ T)
    (heq : (∏ p ∈ U, p) = ∏ p ∈ V, p) : U = V := by
  have hsub (A B : Finset ℕ) (hA : A ⊆ T) (hB : B ⊆ T)
      (hprod : (∏ p ∈ A, p) = ∏ p ∈ B, p) : A ⊆ B := by
    intro p hp
    have hd : p ∣ ∏ q ∈ B, q := hprod ▸ dvd_prod_of_mem _ hp
    obtain ⟨q, hq, hpq⟩ := (hprime p (hA hp)).prime.exists_mem_finset_dvd hd
    have he : p = q := (Nat.prime_dvd_prime_iff_eq (hprime p (hA hp)) (hprime q (hB hq))).mp hpq
    exact he ▸ hq
  exact Subset.antisymm (hsub U V hU hV heq) (hsub V U hV hU heq.symm)

def products (Y k : ℕ) : Finset ℕ :=
  ((smallPrimesUpTo Y).powersetCard k).image (fun T ↦ ∏ p ∈ T, p)

theorem products_card (Y k : ℕ) : (products Y k).card = (Nat.primeCounting Y).choose k := by
  rw [products, card_image_of_injOn]
  · rw [card_powersetCard, PolynomialPrimeCover.card_small_primes]
  · intro U hU V hV heq
    exact product_injective (smallPrimesUpTo Y) (fun p hp ↦ (mem_smallPrimesUpTo.mp hp).1)
      U (mem_powersetCard.mp hU).1 V (mem_powersetCard.mp hV).1 heq

theorem product_properties (Y k n : ℕ) (hY : 1 ≤ Y) (hn : n ∈ products Y k) :
    0 < n ∧ n ≤ Y ^ k ∧ largestPrimeFactor n ≤ Y := by
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hn
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
  have hprime (p : ℕ) (hp : p ∈ T) : p.Prime := (mem_smallPrimesUpTo.mp (hsub hp)).1
  refine ⟨prod_pos (fun p hp ↦ (hprime p hp).pos), ?_, ?_⟩
  · calc
      _ ≤ ∏ _p ∈ T, Y := prod_le_prod (fun p hp ↦ (mem_smallPrimesUpTo.mp (hsub hp)).2)
      _ = _ := by simp only [prod_const, hcard]
  · apply max_le hY
    apply Finset.sup_le
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨q, hq, hpq⟩ := hpprime.prime.exists_mem_finset_dvd (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.le_of_dvd (hprime q hq).pos hpq).trans (mem_smallPrimesUpTo.mp (hsub hq)).2

theorem ordinary_reciprocal_lower (X Y k : ℕ) (hY : 1 ≤ Y) (hheight : Y ^ k ≤ X) :
    ((Nat.primeCounting Y).choose k : ℝ) / Y ≤ primeSum X := by
  have hsub : products Y k ⊆ Icc 1 X := by
    intro n hn
    have hh := product_properties Y k n hY hn
    exact mem_Icc.mpr ⟨hh.1, hh.2.1.trans hheight⟩
  calc
    _ = ∑ _n ∈ products Y k, 1 / (Y : ℝ) := by rw [sum_const, nsmul_eq_mul, products_card]; ring
    _ ≤ ∑ n ∈ products Y k, 1 / (largestPrimeFactor n : ℝ) := sum_le_sum (fun n hn ↦
      one_div_le_one_div_of_le (by exact_mod_cast largestPrimeFactor_pos n)
        (by exact_mod_cast (product_properties Y k n hY hn).2.2))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

theorem choose_lower (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((n : ℝ) / (2 * k)) ^ k ≤ (n.choose k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbase : (n : ℝ) / 2 ≤ ((n + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hh : 2 * (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith only [hh]
  have hfact : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hfactpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  calc
    _ = ((n : ℝ) / 2) ^ k / (k : ℝ) ^ k := by rw [← div_pow]; congr 1; field_simp
    _ ≤ (((n + 1 - k : ℕ) : ℝ) ^ k) / (k : ℝ) ^ k :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)
    _ ≤ (((n + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfactpos hfact
    _ ≤ _ := by exact_mod_cast (Nat.pow_le_choose k n (α := ℝ))

end PaperP1.PrimeProductCensus
