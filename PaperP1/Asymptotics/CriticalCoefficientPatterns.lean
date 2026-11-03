module

public import PaperP1.Arithmetic.CoefficientSplitRadicalPatterns
public import PaperP1.Asymptotics.CriticalGeneralRootPatterns

/-! # A subpower coefficient list absorbs every fixed number of bounded offset patterns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalCoefficientPatterns

open Finset PaperP1.CoefficientSplitRadicalPatterns PaperP1.GeneralSplitRadicalPatternPool

def coefficientMargin (ε : ℝ) (k : ℕ) : ℝ := ε / (2 * ((k : ℝ) + 1))

theorem margin_pos {ε : ℝ} (hε : 0 < ε) (k : ℕ) : 0 < coefficientMargin ε k := by
  dsimp [coefficientMargin]
  positivity

theorem uniform_pool (C ε : ℝ) (k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin ε k →
        ((CoefficientSplitRadicalPatterns.pool k L K Q).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨No, ho⟩ := CriticalGeneralRootPatterns.uniform_offsets C (ε / 2) k K (by positivity)
  refine ⟨max 1 No, by omega, ?_⟩
  intro N hN L hband Q hQ
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
      mul_le_mul (ho N (by omega) L hband) hcode (by positivity) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end PaperP1.CriticalCoefficientPatterns
