module

public import PaperP1.Analysis.BivariateSeriesValue
public import PaperP1.Algebra.BivariateHeightPower
public import PaperP1.Algebra.BivariateTotalDegree

/-! # Vanishing beyond the remaining pole weight gives the actual 1/N bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveTailScaling

open Polynomial PaperP1.BiquadraticFormalNumerator PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree

theorem coefficient_budget (B q K M : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hK : K ≤ 6 * q) (hM : M ≤ 6 * q + 1) :
    2 * (M + 1) * 2 ^ K * (2 * B) ^ M * (B + 1) ^ (300 * q) ≤ (B + 1) ^ (400 * q) := by
  have hbase : 2 ≤ B + 1 := by omega
  have hprefix : 2 * (M + 1) ≤ (B + 1) ^ (6 * q) := by
    calc
      _ ≤ 32 * q + 1 := by omega
      _ ≤ (B + 1) ^ 6 := BivariateHeightPower.linear_dimension B q hq hqB
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have htwo : 2 ^ K ≤ (B + 1) ^ (6 * q) :=
    (Nat.pow_le_pow_left hbase K).trans (Nat.pow_le_pow_right (by omega) hK)
  have hBpow : (2 * B) ^ M ≤ (B + 1) ^ (14 * q) := by
    have hb : 2 * B ≤ (B + 1) ^ 2 := by nlinarith
    calc
      _ ≤ ((B + 1) ^ 2) ^ M := Nat.pow_le_pow_left hb M
      _ = (B + 1) ^ (2 * M) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ (B + 1) ^ (6 * q) * (B + 1) ^ (6 * q) * (B + 1) ^ (14 * q) * (B + 1) ^ (300 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hprefix htwo) hBpow) le_rfl
    _ = (B + 1) ^ (326 * q) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem scaled_geometric_bound (B q K M : ℕ) (N : ℝ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hK : K ≤ 6 * q) (hM : M ≤ 6 * q + 1) (hgap : K + 1 ≤ M) (hN : 1 ≤ N) :
    (2 * N) ^ K * (2 * ((B : ℝ) + 1) ^ (300 * q) * ((M : ℝ) + 1) * ((2 * (B : ℝ)) / N) ^ M) ≤
      ((B : ℝ) + 1) ^ (400 * q) / N := by
  have hNpos : 0 < N := by linarith
  have hratio : N ^ K / N ^ M ≤ 1 / N := by
    apply (div_le_div_iff₀ (pow_pos hNpos M) hNpos).mpr
    rw [one_mul, ← pow_succ]
    exact pow_le_pow_right₀ hN hgap
  have hnum : 2 * ((M : ℝ) + 1) * (2 : ℝ) ^ K * (2 * (B : ℝ)) ^ M *
      ((B : ℝ) + 1) ^ (300 * q) ≤ ((B : ℝ) + 1) ^ (400 * q) := by
    exact_mod_cast coefficient_budget B q K M hq hqB hK hM
  calc
    _ = (2 * ((M : ℝ) + 1) * (2 : ℝ) ^ K * (2 * (B : ℝ)) ^ M * ((B : ℝ) + 1) ^ (300 * q)) *
        (N ^ K / N ^ M) := by rw [mul_pow, div_pow]; ring
    _ ≤ ((B : ℝ) + 1) ^ (400 * q) * (1 / N) := mul_le_mul hnum hratio (by positivity) (by positivity)
    _ = _ := by ring

theorem scaled_series_bound (f : Series) (B q kx ky M : ℕ) (N x y : ℝ)
    (hq : 1 ≤ q) (hqB : q ≤ B) (hkx : kx ≤ 3 * q) (hky : ky ≤ 3 * q)
    (hM : M ≤ 6 * q + 1) (hgap : kx + ky + 1 ≤ M)
    (hN : 8 * (B : ℝ) ≤ N) (hx : N ≤ x) (hy : N ≤ y) (hx₂ : x ≤ 2 * N) (hy₂ : y ≤ 2 * N)
    (hcoeff : ∀ a b, |(coefficient a b f : ℝ)| ≤ ((B : ℝ) + 1) ^ (300 * q) * (2 * (B : ℝ)) ^ (a + b))
    (hzero : ∀ a b, a + b < M → coefficient a b f = 0) :
    ‖x ^ kx * y ^ ky * BivariateSeriesValue.value f (1 / x) (1 / y)‖ ≤
      ((B : ℝ) + 1) ^ (400 * q) / N := by
  have hB : (1 : ℝ) ≤ B := by exact_mod_cast hq.trans hqB
  have hN₁ : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hxp : 0 < x := hNp.trans_le hx
  have hyp : 0 < y := hNp.trans_le hy
  have hξ : |1 / x| ≤ 1 / N := by
    rw [abs_of_pos (one_div_pos.mpr hxp)]
    exact one_div_le_one_div_of_le hNp hx
  have hη : |1 / y| ≤ 1 / N := by
    rw [abs_of_pos (one_div_pos.mpr hyp)]
    exact one_div_le_one_div_of_le hNp hy
  have hsmall : (2 * (B : ℝ)) * (1 / N) ≤ 1 / 4 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hNp).mpr
    linarith
  have ht := BivariateSeriesValue.vanishing_tail_bound f (1 / x) (1 / y) (((B : ℝ) + 1) ^ (300 * q))
    (2 * (B : ℝ)) (1 / N) M (by positivity) (by positivity) (by positivity) hξ hη hsmall hcoeff hzero
  have htail : ‖BivariateSeriesValue.value f (1 / x) (1 / y)‖ ≤
      2 * ((B : ℝ) + 1) ^ (300 * q) * ((M : ℝ) + 1) * ((2 * (B : ℝ)) / N) ^ M := by
    simpa only [mul_one_div] using ht
  have hpole : ‖x ^ kx * y ^ ky‖ ≤ (2 * N) ^ (kx + ky) := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (pow_pos hxp _) (pow_pos hyp _)), pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hxp.le hx₂ _) (pow_le_pow_left₀ hyp.le hy₂ _)
      (pow_nonneg hyp.le _) (pow_nonneg (by positivity) _)
  rw [norm_mul]
  exact (mul_le_mul hpole htail (norm_nonneg _) (pow_nonneg (by positivity) _)).trans
    (scaled_geometric_bound B q (kx + ky) M N hq hqB (by omega) hM hgap hN₁)

theorem remaining_order_budget (D : ℤ[X][X]) (q : ℕ)
    (hx : degreeX D ≤ 3 * q) (hy : degreeY D ≤ 3 * q) :
    (3 * q - degreeX D) + (3 * q - degreeY D) + totalDegree D + 1 ≤ 6 * q + 1 ∧
      (3 * q - degreeX D) + (3 * q - degreeY D) + 1 ≤
        (3 * q - degreeX D) + (3 * q - degreeY D) + totalDegree D + 1 := by
  have hd := totalDegree_le_partial D
  omega

end PaperP1.PrimitiveTailScaling
