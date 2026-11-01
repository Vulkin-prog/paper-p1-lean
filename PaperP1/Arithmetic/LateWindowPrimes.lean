module

public import PaperP1.Arithmetic.OldValuePrimeBudget

/-! # The actual three-band prime cover for values in the upper half block

A divisor of a value between 3N/2 and 2N has multiplier one, two, or
at least three. The corresponding prime cover is the finite source of
the coefficient 17/12 in companion T19.9.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LateWindowPrimes

open Finset PaperP1.DefectCounting PaperP1.LocalDefectBound
  PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget

def low (N : ℕ) : Finset ℕ := smallPrimesUpTo (2 * N / 3)

def middle (N : ℕ) : Finset ℕ :=
  smallPrimesUpTo N \ smallPrimesUpTo (3 * N / 4 - 1)

def high (N : ℕ) : Finset ℕ :=
  smallPrimesUpTo (2 * N) \ smallPrimesUpTo (3 * N / 2 - 1)

def cover (N : ℕ) : Finset ℕ := low N ∪ middle N ∪ high N

theorem smallPrimes_mono {a b : ℕ} (hab : a ≤ b) : smallPrimesUpTo a ⊆ smallPrimesUpTo b := by
  intro p hp
  obtain ⟨hp, hpa⟩ := mem_smallPrimesUpTo.mp hp
  exact mem_smallPrimesUpTo.mpr ⟨hp, hpa.trans hab⟩

theorem cover_prime (N : ℕ) : ∀ p ∈ cover N, Nat.Prime p := by
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · rcases mem_union.mp hp with hp | hp
    · exact (mem_smallPrimesUpTo.mp hp).1
    · exact (mem_smallPrimesUpTo.mp (mem_sdiff.mp hp).1).1
  · exact (mem_smallPrimesUpTo.mp (mem_sdiff.mp hp).1).1

theorem prime_divisor_cases {N n p : ℕ} (hlo : 3 * N ≤ 2 * n)
    (hhi : n < 2 * N) (hpn : p ∣ n) :
    3 * p ≤ 2 * N ∨ (3 * N ≤ 4 * p ∧ p ≤ N) ∨ (3 * N ≤ 2 * p ∧ p < 2 * N) := by
  obtain ⟨k, hk⟩ := hpn
  have hk0 : 0 < k := by nlinarith
  by_cases hk1 : k = 1
  · right
    right
    subst k
    simp only [Nat.mul_one] at hk
    omega
  · by_cases hk2 : k = 2
    · right
      left
      subst k
      constructor <;> omega
    · left
      have hk3 : 3 ≤ k := by omega
      have hmul := Nat.mul_le_mul_left p hk3
      nlinarith

theorem divisor_mem_cover {N n p : ℕ} (hlo : 3 * N ≤ 2 * n)
    (hhi : n < 2 * N) (hp : Nat.Prime p) (hpn : p ∣ n) : p ∈ cover N := by
  rcases prime_divisor_cases hlo hhi hpn with h | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact mem_union_left _ (mem_union_left _ (mem_smallPrimesUpTo.mpr ⟨hp, by omega⟩))
  · apply mem_union_left
    apply mem_union_right
    apply mem_sdiff.mpr
    refine ⟨mem_smallPrimesUpTo.mpr ⟨hp, hhi⟩, ?_⟩
    intro hbad
    have hbad := (mem_smallPrimesUpTo.mp hbad).2
    have hp2 := hp.two_le
    omega
  · apply mem_union_right
    apply mem_sdiff.mpr
    refine ⟨mem_smallPrimesUpTo.mpr ⟨hp, hhi.le⟩, ?_⟩
    intro hbad
    have hbad := (mem_smallPrimesUpTo.mp hbad).2
    have hp2 := hp.two_le
    omega

theorem oldPrimes_subset {N : ℕ} {R : Finset ℕ}
    (hR : ∀ n ∈ R, 3 * N ≤ 2 * n ∧ n < 2 * N) :
    oldPrimes R ⊆ cover N := by
  intro p hp
  obtain ⟨n, hn, hp⟩ := mem_biUnion.mp hp
  have h := hR n hn
  exact divisor_mem_cover h.1 h.2 (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)

theorem middle_card (N : ℕ) :
    (middle N).card = primeCount N - primeCount (3 * N / 4 - 1) := by
  exact card_sdiff_of_subset (smallPrimes_mono (by omega))

theorem high_card (N : ℕ) :
    (high N).card = primeCount (2 * N) - primeCount (3 * N / 2 - 1) := by
  exact card_sdiff_of_subset (smallPrimes_mono (by omega))

theorem cover_card (N : ℕ) :
    (cover N).card ≤ primeCount (2 * N / 3) +
      (primeCount N - primeCount (3 * N / 4 - 1)) +
      (primeCount (2 * N) - primeCount (3 * N / 2 - 1)) := by
  have h1 := card_union_le (low N) (middle N)
  have h2 := card_union_le (low N ∪ middle N) (high N)
  rw [middle_card] at h1
  rw [high_card] at h2
  change (cover N).card ≤ _ at h2
  simpa only [low, primeCount] using h2.trans (Nat.add_le_add_right h1 _)

end PaperP1.LateWindowPrimes
