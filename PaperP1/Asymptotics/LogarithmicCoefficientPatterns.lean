module

public import PaperP1.Asymptotics.CriticalCoefficientPatterns

/-! # Offset and coefficient pattern pools under an upper logarithmic width alone -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicCoefficientPatterns

open Finset PaperP1.CoefficientSplitRadicalPatterns PaperP1.GeneralSplitRadicalPatternPool PaperP1.CriticalCoefficientPatterns

theorem uniform_offsets (D ε : ℝ) (k K : ℕ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      (((leftPatterns k L K ×ˢ rightPatterns k L K).card : ℕ) : ℝ) ≤ (N : ℝ) ^ ε := by
  let A := (((K + 1) * 4 ^ K) ^ k) ^ 2
  obtain ⟨Np, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    D hD (A : ℝ) (K * k + K * k) ε hε
  refine ⟨Np, ?_⟩
  intro N hN L hwidth
  have hbound := hp N hN L hwidth
  have hcard : (((leftPatterns k L K ×ˢ rightPatterns k L K).card : ℕ) : ℝ) ≤
      (A : ℝ) * (L + 1 : ℝ) ^ (K * k + K * k) := by exact_mod_cast offset_card_bound k L K
  exact hcard.trans (by simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤
    (A : ℝ) * (L + 1 : ℝ) ^ (K * k + K * k))] using hbound)

theorem uniform_pool (D ε : ℝ) (k K : ℕ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin ε k →
        ((CoefficientSplitRadicalPatterns.pool k L K Q).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨No, ho⟩ := uniform_offsets D (ε / 2) k K hD (by positivity)
  refine ⟨max 1 No, by omega, ?_⟩
  intro N hN L hwidth Q hQ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by positivity
  have hη : 0 < coefficientMargin ε k := margin_pos hε k
  have heq : coefficientMargin ε k * (2 * ((k : ℝ) + 1)) = ε :=
    div_mul_cancel₀ _ (by positivity)
  have hexp : coefficientMargin ε k * (k : ℝ) ≤ ε / 2 := by nlinarith only [hη, heq]
  have hcode : (Q.card : ℝ) ^ k ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ ((N : ℝ) ^ coefficientMargin ε k) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ k
      _ = (N : ℝ) ^ (coefficientMargin ε k * (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hexp
  calc
    _ = (((leftPatterns k L K ×ˢ rightPatterns k L K).card : ℕ) : ℝ) * (Q.card : ℝ) ^ k := by
      rw [card_pool, Nat.cast_mul, Nat.cast_pow]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul (ho N (by omega) L hwidth) hcode (by positivity) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end PaperP1.LogarithmicCoefficientPatterns
