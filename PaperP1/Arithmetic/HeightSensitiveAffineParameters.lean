module

public import PaperP1.Arithmetic.DegreeUniformAffineParameters

/-! # A variable coefficient-height obstruction for an unsheared integer box -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightSensitiveAffineParameters

open Polynomial BivariateDegrees BivariateHeight

theorem obstruction_nat (D N κ a b h : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (ha : a ≤ D) (hb : b ≤ D) (hh : h ≤ N ^ κ) :
    (a + 1) * (b + 1) * b * h * N ^ (a + 1) * N ^ b ≤ N ^ (κ + 8 * D + 8) := by
  have hN : 2 ≤ N := hD.trans hDN
  have hN1 : 1 ≤ N := by omega
  have hplus : D + 1 ≤ N ^ 2 := by nlinarith
  have haplus : a + 1 ≤ N ^ 2 := (Nat.add_le_add_right ha 1).trans hplus
  have hbplus : b + 1 ≤ N ^ 2 := (Nat.add_le_add_right hb 1).trans hplus
  have hcoef : (a + 1) * (b + 1) * b ≤ N ^ 5 := by
    calc
      _ ≤ N ^ 2 * N ^ 2 * N := Nat.mul_le_mul (Nat.mul_le_mul haplus hbplus) (hb.trans hDN)
      _ = _ := by ring
  calc
    _ = ((a + 1) * (b + 1) * b) * h * (N ^ (a + 1) * N ^ b) := by ring
    _ ≤ N ^ 5 * N ^ κ * (N ^ (a + 1) * N ^ b) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hcoef hh)
    _ = N ^ (5 + κ + (a + 1 + b)) := by rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hN1 (by omega)

theorem obstruction_real (D N κ : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (G : ℤ[X][X]) (ha : degreeX G ≤ D) (hb : degreeY G ≤ D)
    (hh : height G ≤ N ^ κ) :
    (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      (N : ℝ) ^ (degreeX G + 1) * (N : ℝ) ^ degreeY G ≤ ((N ^ (κ + 8 * D + 8) : ℕ) : ℝ) := by
  exact_mod_cast obstruction_nat D N κ (degreeX G) (degreeY G) (height G) hD hDN ha hb hh

end PaperP1.HeightSensitiveAffineParameters
