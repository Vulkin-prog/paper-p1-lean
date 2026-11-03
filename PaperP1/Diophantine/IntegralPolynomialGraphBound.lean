module

public import PaperP1.Algebra.IntegerPolynomialGrowth

/-! # A polynomial graph of degree at least two cannot have large integral points of comparable coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralPolynomialGraphBound

open Polynomial

theorem abscissa_bound (a M : ℕ) (ha : 2 ≤ a) (P : ℤ[X]) (hdeg : P.natDegree = a)
    (hcoeff : ∀ n, (P.coeff n).natAbs ≤ M) (q₀ x y : ℤ) (hq : q₀.natAbs ≤ M)
    (hy : y.natAbs ≤ 2 * x.natAbs) (hpoint : P.eval x = y * q₀) :
    x.natAbs ≤ (a + 2) * M := by
  by_cases hx0 : x.natAbs = 0
  · simp only [hx0, Nat.zero_le]
  have hx : 1 ≤ x.natAbs := by omega
  have hpos : 0 < x.natAbs ^ (a - 1) := pow_pos (by omega) _
  have hpower : x.natAbs ≤ x.natAbs ^ (a - 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by omega : 1 ≤ a - 1)
  have hvalue : (P.eval x).natAbs ≤ 2 * x.natAbs * M := by
    rw [hpoint, Int.natAbs_mul]
    exact Nat.mul_le_mul hy hq
  have hlow := IntegerPolynomialGrowth.lower_power_bound P a M (by omega) hdeg hcoeff x hx
  have hexp : x.natAbs ^ a = x.natAbs * x.natAbs ^ (a - 1) := by
    calc
      x.natAbs ^ a = x.natAbs ^ ((a - 1) + 1) := congrArg (fun n ↦ x.natAbs ^ n) (by omega)
      _ = _ := pow_succ' _ _
  have hcancel : x.natAbs * x.natAbs ^ (a - 1) ≤ ((a + 2) * M) * x.natAbs ^ (a - 1) := by
    rw [← hexp]
    calc
      x.natAbs ^ a ≤ 2 * x.natAbs * M + a * M * x.natAbs ^ (a - 1) :=
        hlow.trans (Nat.add_le_add_right hvalue _)
      _ ≤ 2 * x.natAbs ^ (a - 1) * M + a * M * x.natAbs ^ (a - 1) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right M (Nat.mul_le_mul_left 2 hpower)) _
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hcancel hpos

end PaperP1.IntegralPolynomialGraphBound
