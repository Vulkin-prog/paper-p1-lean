module

public import PaperP1.Arithmetic.DyadicEndpointPairs

/-! # Literal polynomial bounds for source size and dyadic endpoint pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialEndpointBudget

open Finset PaperP1.DyadicEndpointPairs

theorem source_size_bound {a B H J : ℕ} (hB : 1 ≤ B) (hH : H ≤ B ^ J) :
    a * (2 * H * (B + 1)) + B ≤ (4 * a + 1) * B ^ (J + 1) := by
  have hBpow : B ≤ B ^ (J + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ J + 1 by omega)
  have hmul := Nat.mul_le_mul hH (show B + 1 ≤ 2 * B by omega)
  have hbase : H * (B + 1) ≤ 2 * B ^ (J + 1) := by
    rw [pow_succ]
    nlinarith only [hmul]
  have hscaled := Nat.mul_le_mul_left (2 * a) hbase
  nlinarith only [hscaled, hBpow]

theorem exceptional_polynomial {N a b L H J : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (hJ : 1 ≤ J) (hH : H ≤ (L + 1) ^ J) :
    (exceptional N a b L ((L + 1) + 2 * H)).card ≤
      (6 * (a + b) + 2) * (L + 1) ^ (J + 2) := by
  let B : ℕ := L + 1
  change H ≤ B ^ J at hH
  have hB : 1 ≤ B := by omega
  have hBpow : B ≤ B ^ J := by simpa only [pow_one] using Nat.pow_le_pow_right hB hJ
  have hR : B + 2 * H ≤ 3 * B ^ J := by omega
  have hpower : B ^ 2 * B ^ J = B ^ (J + 2) := by rw [← pow_add]; congr 1; omega
  have hmain : B ^ 2 * (2 * (a + b) * (B + 2 * H)) ≤ 6 * (a + b) * B ^ (J + 2) := by
    calc
      _ ≤ B ^ 2 * (2 * (a + b) * (3 * B ^ J)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hR)
      _ = _ := by rw [← hpower]; ring
  have hBpow2 : B ^ 2 ≤ B ^ (J + 2) := Nat.pow_le_pow_right hB (by omega)
  have hcard := exceptional_card (L := L) (R := B + 2 * H) hN ha hb
  calc
    _ ≤ B ^ 2 * (2 * (a + b) * (B + 2 * H) + 2) := hcard
    _ = B ^ 2 * (2 * (a + b) * (B + 2 * H)) + 2 * B ^ 2 := by ring
    _ ≤ 6 * (a + b) * B ^ (J + 2) + 2 * B ^ (J + 2) :=
      Nat.add_le_add hmain (Nat.mul_le_mul_left 2 hBpow2)
    _ = _ := by dsimp [B]; ring

end PaperP1.PolynomialEndpointBudget
