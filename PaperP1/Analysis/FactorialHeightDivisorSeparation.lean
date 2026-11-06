module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Positivity

/-! # A fixed factorial constant turns the sharp exponent inequality into literal integer separation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialHeightDivisorSeparation

theorem separation (s W E H Q : ℕ) (hE : 0 < E) (hH : 1 ≤ H) (α : ℝ)
    (hW : (W : ℝ) ≤ α * (E : ℝ))
    (hQ : ((s.factorial + 1 : ℕ) : ℝ) * (H : ℝ) ^ α ≤ (Q : ℝ)) :
    s.factorial * H ^ W < Q ^ E := by
  let B : ℕ := s.factorial + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBpow : s.factorial < B ^ E :=
    (Nat.lt_succ_self s.factorial).trans_le (le_self_pow hB (Nat.ne_of_gt hE))
  have hBreal : (s.factorial : ℝ) < (B : ℝ) ^ E := by exact_mod_cast hBpow
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hpower : ((H : ℝ) ^ α) ^ E = (H : ℝ) ^ (α * (E : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg H)]
  have hheight : (H : ℝ) ^ W ≤ ((H : ℝ) ^ α) ^ E := by
    rw [hpower]
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hHreal hW
  have hpow : ((B : ℝ) * (H : ℝ) ^ α) ^ E ≤ (Q : ℝ) ^ E :=
    pow_le_pow_left₀ (by positivity) hQ E
  have hreal : (s.factorial : ℝ) * (H : ℝ) ^ W < (Q : ℝ) ^ E := by
    calc
      _ ≤ (s.factorial : ℝ) * ((H : ℝ) ^ α) ^ E :=
        mul_le_mul_of_nonneg_left hheight (Nat.cast_nonneg _)
      _ < (B : ℝ) ^ E * ((H : ℝ) ^ α) ^ E :=
        mul_lt_mul_of_pos_right hBreal (pow_pos (Real.rpow_pos_of_pos hHpos α) E)
      _ = ((B : ℝ) * (H : ℝ) ^ α) ^ E := (mul_pow _ _ _).symm
      _ ≤ _ := hpow
  exact_mod_cast hreal

end PaperP1.FactorialHeightDivisorSeparation
