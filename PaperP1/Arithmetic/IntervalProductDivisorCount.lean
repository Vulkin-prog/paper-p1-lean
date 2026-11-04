module

public import PaperP1.Arithmetic.IntegerRealIntervalCount
public import PaperP1.Arithmetic.DivisorSubpolynomial

/-! # Actual interval indices are positive divisors in each integer-product fibre -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntervalProductDivisorCount

open Finset

theorem product_divisor_mem (k : ℕ) (b : ℤ) (hproduct : b * (k : ℤ) ≠ 0) :
    k ∈ (b * (k : ℤ)).natAbs.divisors := by
  apply Nat.mem_divisors.mpr
  refine ⟨?_, Int.natAbs_ne_zero.mpr hproduct⟩
  have hdiv : (k : ℤ) ∣ b * (k : ℤ) := ⟨b, by ring⟩
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv

theorem finite_interval_count (I : Finset ℕ) (a b : ℕ → ℤ) (A B R H : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hk : ∀ k ∈ I, 0 < k) (hb : ∀ k ∈ I, b k ≠ 0)
    (ha : ∀ k ∈ I, |(a k : ℝ)| ≤ A)
    (hres : ∀ k ∈ I, |((b k * (k : ℤ) : ℤ) : ℝ) - R * (a k : ℝ)| ≤ B)
    (hdiv : ∀ k ∈ I, ((b k * (k : ℤ)).natAbs.divisors.card : ℝ) ≤ H) :
    (I.card : ℝ) ≤ (2 * A + 1) * (2 * B + 1) * H := by
  classical
  let f : ℕ → ℤ × ℤ := fun k ↦ (a k, b k * (k : ℤ))
  let J := I.image f
  have hproduct (k : ℕ) (hki : k ∈ I) : b k * (k : ℤ) ≠ 0 :=
    mul_ne_zero (hb k hki) (by exact_mod_cast (hk k hki).ne')
  have hstrip : (J.card : ℝ) ≤ (2 * A + 1) * (2 * B + 1) := by
    apply IntegerRealIntervalCount.strip_card J A B R hA hB
    intro p hp
    obtain ⟨k, hki, rfl⟩ := mem_image.mp hp
    exact ⟨ha k hki, hres k hki⟩
  have hfiber (p : ℤ × ℤ) (hp : p ∈ J) : ((I.filter (fun k ↦ f k = p)).card : ℝ) ≤ H := by
    obtain ⟨k₀, hk₀, hfp⟩ := mem_image.mp hp
    have hn : b k₀ * (k₀ : ℤ) = p.2 := congrArg Prod.snd hfp
    have hsub : I.filter (fun k ↦ f k = p) ⊆ p.2.natAbs.divisors := by
      intro k hkf
      obtain ⟨hki, hkp⟩ := mem_filter.mp hkf
      have hkn : b k * (k : ℤ) = p.2 := congrArg Prod.snd hkp
      rw [← hkn]
      exact product_divisor_mem k (b k) (hproduct k hki)
    have hcount : ((I.filter (fun k ↦ f k = p)).card : ℝ) ≤ (p.2.natAbs.divisors.card : ℝ) :=
      by exact_mod_cast card_le_card hsub
    exact hcount.trans (by simpa only [hn] using hdiv k₀ hk₀)
  calc
    _ = ∑ p ∈ J, ((I.filter (fun k ↦ f k = p)).card : ℝ) := by exact_mod_cast card_eq_sum_card_image f I
    _ ≤ ∑ _p ∈ J, H := sum_le_sum hfiber
    _ = (J.card : ℝ) * H := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hstrip hH

theorem product_height (N κ k : ℕ) (hN : 2 ≤ N) (hk : k ≤ 2 * N) (b : ℤ)
    (hb : b.natAbs ≤ N ^ κ) : (b * (k : ℤ)).natAbs ≤ N ^ (κ + 2) := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  calc
    _ ≤ N ^ κ * (2 * N) := Nat.mul_le_mul hb hk
    _ = 2 * N ^ (κ + 1) := by rw [pow_succ']; ring
    _ ≤ N * N ^ (κ + 1) := Nat.mul_le_mul_right _ hN
    _ = _ := (pow_succ' N (κ + 1)).symm

theorem uniform_interval_count (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ I : Finset ℕ, ∀ a b : ℕ → ℤ, ∀ A B R : ℝ,
      0 ≤ A → 0 ≤ B →
      (∀ k ∈ I, 0 < k ∧ k ≤ 2 * N) → (∀ k ∈ I, b k ≠ 0 ∧ (b k).natAbs ≤ N ^ κ) →
      (∀ k ∈ I, |(a k : ℝ)| ≤ A) →
      (∀ k ∈ I, |((b k * (k : ℤ) : ℤ) : ℝ) - R * (a k : ℝ)| ≤ B) →
      (I.card : ℝ) ≤ (2 * A + 1) * (2 * B + 1) * (N : ℝ) ^ ε := by
  obtain ⟨Nd, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually (κ + 2) ε hε
  refine ⟨max 2 Nd, ?_⟩
  intro N hN I a b A B R hA hB hk hb ha hres
  apply finite_interval_count I a b A B R ((N : ℝ) ^ ε) hA hB (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (fun k hki ↦ (hk k hki).1) (fun k hki ↦ (hb k hki).1) ha hres
  intro k hki
  exact hd N (by omega) _ (product_height N κ k (by omega) (hk k hki).2 (b k) (hb k hki).2)

end PaperP1.IntervalProductDivisorCount
