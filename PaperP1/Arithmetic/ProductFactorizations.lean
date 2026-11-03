module

public import PaperP1.Arithmetic.DivisorSubpolynomial
public import Mathlib.Data.Fintype.BigOperators

/-! # Actual ordered positive factorizations of a fixed product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProductFactorizations

open Finset

def pool (k Q : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k ↦ Q.divisors).filter fun q ↦ ∏ j, q j = Q

theorem mem_pool (k Q : ℕ) (hQ : 0 < Q) (q : Fin k → ℕ) :
    q ∈ pool k Q ↔ ∏ j, q j = Q := by
  constructor
  · intro hq
    exact (mem_filter.mp hq).2
  · intro hprod
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, hprod⟩
    intro j
    apply Nat.mem_divisors.mpr
    exact ⟨hprod ▸ dvd_prod_of_mem q (mem_univ j), hQ.ne'⟩

theorem entry_pos {k Q : ℕ} {q : Fin k → ℕ} (hq : q ∈ pool k Q) (j : Fin k) : 0 < q j := by
  have hd := Fintype.mem_piFinset.mp (mem_filter.mp hq).1 j
  exact Nat.pos_of_mem_divisors hd

theorem card_le (k Q : ℕ) : (pool k Q).card ≤ Q.divisors.card ^ k := by
  exact (card_filter_le _ _).trans_eq (Fintype.card_piFinset_const _ _)

theorem uniform_count (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : ℕ, Q ≤ N ^ K →
      ((pool k Q).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually K
    (ε / (k + 1 : ℕ)) (by positivity)
  refine ⟨max 2 ND, by omega, ?_⟩
  intro N hN Q hQ
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiv := hd N (by omega) Q hQ
  calc
    _ ≤ (Q.divisors.card : ℝ) ^ k := by exact_mod_cast card_le k Q
    _ ≤ ((N : ℝ) ^ (ε / (k + 1 : ℕ))) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv k
    _ = (N : ℝ) ^ ((ε / (k + 1 : ℕ)) * k) := by rw [← Real.rpow_mul_natCast (by positivity)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hn
      have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hk).mpr
      push_cast
      nlinarith

end PaperP1.ProductFactorizations
