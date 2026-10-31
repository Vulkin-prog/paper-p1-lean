module

public import PaperP1.Analysis.PartialPowerSum
public import Mathlib.Analysis.Real.Sqrt

/-!
# Finite square-root fibres and Rankin powers

The real and natural square-root comparisons and the finite-product rewrite
are adapted from PaperCV11/RankinTilt.lean, by Vulkin-prog, Apache-2.0,
commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 0e160cd09e337d5b6142c75524a2da9da7ec5584.
The exponent is written as σ instead of 1-ζ. The all-fibres comparison below
also covers support products above X, where the actual natural fibre is empty.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RankinComparison

open Finset

theorem sqrt_div_le_rankin {X s σ : ℝ} (hs : 1 ≤ s) (hsX : s ≤ X)
    (hσ : 1 / 2 ≤ σ) : Real.sqrt (X / s) ≤ X ^ σ * s ^ (-σ) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hX0 : 0 ≤ X := (zero_le_one.trans hs).trans hsX
  have hquot : 1 ≤ X / s := by
    apply (le_div_iff₀ hspos).mpr
    simpa using hsX
  calc
    Real.sqrt (X / s) = (X / s) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ ≤ (X / s) ^ σ := Real.rpow_le_rpow_of_exponent_le hquot hσ
    _ = X ^ σ * s ^ (-σ) := by
      rw [Real.div_rpow hX0 hspos.le, div_eq_mul_inv, ← Real.rpow_neg hspos.le]

theorem cast_sqrt_div_le_rankin {X s : ℕ} {σ : ℝ} (hs : 1 ≤ s)
    (hσ : 1 / 2 ≤ σ) :
    (Nat.sqrt (X / s) : ℝ) ≤ (X : ℝ) ^ σ * (s : ℝ) ^ (-σ) := by
  by_cases hsX : s ≤ X
  · calc
      _ ≤ Real.sqrt (X / s : ℕ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt ((X : ℝ) / (s : ℝ)) := Real.sqrt_le_sqrt Nat.cast_div_le
      _ ≤ _ := sqrt_div_le_rankin (by exact_mod_cast hs) (by exact_mod_cast hsX) hσ
  · rw [Nat.div_eq_of_lt (by omega : X < s)]
    simp only [Nat.sqrt_zero, Nat.cast_zero]
    positivity

theorem cast_prod_rpow (S : Finset ℕ) (σ : ℝ) :
    (↑(S.prod id) : ℝ) ^ (-σ) = ∏ p ∈ S, (p : ℝ) ^ (-σ) := by
  rw [Nat.cast_prod]
  simp only [id_eq]
  exact (Real.finsetProd_rpow S (fun p : ℕ ↦ (p : ℝ))
    (fun p _ ↦ Nat.cast_nonneg p) (-σ)).symm

end PaperP1.RankinComparison
