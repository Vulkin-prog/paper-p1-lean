module

public import PaperP1.Arithmetic.IntervalCongruence
public import Mathlib.Tactic.Linarith

/-! # A two-sided finite error for one integer residue class -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.IntervalResidueError

open Finset

theorem lower_bound (a b v r : ℤ) (hr : 0 < r) :
    (((b - a : ℤ) : ℚ) / (r : ℚ)) - 1 ≤
      (({x ∈ Ico a b | x ≡ v [ZMOD r]}).card : ℚ) := by
  have hcardZ : ⌈((b : ℚ) - v) / r⌉ - ⌈((a : ℚ) - v) / r⌉ ≤
      (({x ∈ Ico a b | x ≡ v [ZMOD r]}).card : ℤ) := by
    rw [Int.Ico_filter_modEq_card a b hr v]
    exact le_max_left _ _
  have hcardQ : (⌈((b : ℚ) - v) / r⌉ : ℚ) - (⌈((a : ℚ) - v) / r⌉ : ℚ) ≤
      (({x ∈ Ico a b | x ≡ v [ZMOD r]}).card : ℚ) := by exact_mod_cast hcardZ
  have hb : ((b : ℚ) - v) / r ≤ (⌈((b : ℚ) - v) / r⌉ : ℚ) := Int.le_ceil _
  have ha : (⌈((a : ℚ) - v) / r⌉ : ℚ) ≤ ((a : ℚ) - v) / r + 1 := (Int.ceil_lt_add_one _).le
  have hdiff : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
    rw [Int.cast_sub]
    ring
  linarith

theorem abs_error (a b v r : ℤ) (hr : 0 < r) (hab : a ≤ b) :
    |(({x ∈ Ico a b | x ≡ v [ZMOD r]}).card : ℚ) - ((b - a : ℤ) : ℚ) / r| ≤ 1 := by
  have hlo := lower_bound a b v r hr
  have hhi := Channels.card_Ico_modEq_cast_le_div_add_one a b v r hr hab
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PaperP1.IntervalResidueError
