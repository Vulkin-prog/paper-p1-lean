module

public import PaperP1.Arithmetic.DivisorSubpolynomial

/-! # Subpower prime-support code counts at every fixed polynomial height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialPrimeFactorPowers

open Finset

theorem two_pow_le_divisors (m : ℕ) (hm : 0 < m) : 2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm.ne']
  calc
    _ = ∏ _p ∈ m.primeFactors, 2 := by simp only [prod_const]
    _ ≤ _ := by
      apply prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _)
      intro p hp
      obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
      have he := (hprime.dvd_iff_one_le_factorization hm.ne').mp hdiv
      omega

theorem uniform_four_pow (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ, 0 < m → m ≤ N ^ K →
      (4 : ℝ) ^ m.primeFactors.card ≤ (N : ℝ) ^ ε := by
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually K (ε / 2) (by positivity)
  refine ⟨max 2 ND, by omega, ?_⟩
  intro N hN m hm hheight
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have htwo : (2 : ℝ) ^ m.primeFactors.card ≤ m.divisors.card := by
    exact_mod_cast two_pow_le_divisors m hm
  have hdiv := hd N (by omega) m hheight
  calc
    _ = ((2 : ℝ) ^ m.primeFactors.card) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 _, pow_mul]
    _ ≤ (m.divisors.card : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) htwo 2
    _ ≤ ((N : ℝ) ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv 2
    _ = _ := by rw [pow_two, ← Real.rpow_add hn]; congr 1; ring

end PaperP1.PolynomialPrimeFactorPowers
