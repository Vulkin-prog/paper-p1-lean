module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Exact cancellation of the source embedding degree in the covering exponents at height H^E -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceOrdinaryCoverPower

theorem sqrt_degree (k E : ℕ) : Real.sqrt ((2 ^ k * E ^ 2 : ℕ) : ℝ) =
    Real.sqrt ((2 : ℝ) ^ k) * (E : ℝ) := by
  have he : ((2 ^ k * E ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ k * (E : ℝ) ^ 2 := by norm_cast
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg E)]

theorem height_power (k E H : ℕ) (hE : 0 < E) (a δ : ℝ) :
    ((H ^ E : ℕ) : ℝ) ^ (a / Real.sqrt ((2 ^ k * E ^ 2 : ℕ) : ℝ) + δ / (E : ℝ)) =
      (H : ℝ) ^ (a / Real.sqrt ((2 : ℝ) ^ k) + δ) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg H)]
  congr 1
  rw [sqrt_degree]
  have hE0 : (E : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hE
  have hs0 : Real.sqrt ((2 : ℝ) ^ k) ≠ 0 := by positivity
  field_simp

end PaperP1.SourceOrdinaryCoverPower
