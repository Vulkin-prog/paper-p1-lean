module

public import PaperP1.Arithmetic.TwoAdjacentSmallKernels
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # The lower count for two individually small odd kernels holds for every beta greater than one half -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelLower

open Finset PaperP1.TwoAdjacentSmallKernels

def squareScale (β : ℝ) (N : ℕ) : ℕ := Nat.ceil (2 * (N : ℝ) ^ ((1 - β) / 2))

theorem scale_data {β : ℝ} (hβ : β < 1) {N : ℕ} (hN : 2 ≤ N) :
    0 < squareScale β N ∧
      (squareScale β N : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ (1 - β) ∧
      (squareScale β N : ℝ) ^ 4 ≤ 81 * (N : ℝ) ^ (2 - 2 * β) ∧
      2 * (N : ℝ) ≤ (N : ℝ) ^ β * (squareScale β N : ℝ) ^ 2 ∧
      (N : ℝ) ^ β / 36000 ≤ (N : ℝ) / (4000 * (squareScale β N : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let R := (N : ℝ) ^ ((1 - β) / 2)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (by linarith only [hβ])
  have hceilLo : 2 * R ≤ (squareScale β N : ℝ) := Nat.le_ceil _
  have hceilHi : (squareScale β N : ℝ) ≤ 3 * R := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ 2 * R by positivity)).le
    change (squareScale β N : ℝ) ≤ 2 * R + 1 at hh
    linarith only [hh, hR]
  have hDpos : 0 < squareScale β N := by
    have hh : (0 : ℝ) < squareScale β N := by linarith only [hceilLo, hR]
    exact_mod_cast hh
  have hR2 : R ^ 2 = (N : ℝ) ^ (1 - β) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hR4 : R ^ 4 = (N : ℝ) ^ (2 - 2 * β) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hD2 : (squareScale β N : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ (1 - β) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (squareScale β N)) hceilHi 2
    nlinarith only [hh, hR2]
  have hD4 : (squareScale β N : ℝ) ^ 4 ≤ 81 * (N : ℝ) ^ (2 - 2 * β) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (squareScale β N)) hceilHi 4
    nlinarith only [hh, hR4]
  have hpow : (N : ℝ) ^ β * (N : ℝ) ^ (1 - β) = N := by
    rw [← Real.rpow_add hn]
    norm_num
  have hbudget : 2 * (N : ℝ) ≤ (N : ℝ) ^ β * (squareScale β N : ℝ) ^ 2 := by
    have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 * R by positivity) hceilLo 2
    have hmul := mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hn.le β)
    rw [show (2 * R) ^ 2 = 4 * R ^ 2 by ring, hR2] at hmul
    nlinarith only [hmul, hpow, hn.le]
  have hlower : (N : ℝ) ^ β / 36000 ≤ (N : ℝ) / (4000 * (squareScale β N : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4000 * (squareScale β N : ℝ) ^ 2)).mpr
    have hmul := mul_le_mul_of_nonneg_left hD2 (Real.rpow_nonneg hn.le β)
    nlinarith only [hmul, hpow]
  exact ⟨hDpos, hD2, hD4, hbudget, hlower⟩

theorem uniform_lower (β ε : ℝ) (hβlo : 1 / 2 < β) (hβhi : β < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H : ℕ,
      (N : ℝ) ^ (β - ε) ≤ ((admissible N H ((N : ℝ) ^ β)).card : ℝ) := by
  obtain ⟨NG, hg⟩ := HalfCountSchedule.factor_absorption 3240000 (2 - 2 * β) (2 * β - 1) (by linarith only [hβlo])
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually 2 (ε / 4) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 36000 (β - ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NG (max ND NA)), by omega, ?_⟩
  intro N hN H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hDpos, _hD2, hD4, hbudget, hlower⟩ := scale_data hβhi (by omega : 2 ≤ N)
  have hlarge : 40000 * squareScale β N ^ 4 ≤ N := by
    have hgrowth : 3240000 * (N : ℝ) ^ (2 - 2 * β) ≤ N := by
      simpa only [show (2 - 2 * β) + (2 * β - 1) = (1 : ℝ) by ring, Real.rpow_one] using hg N (by omega)
    have hh : 40000 * (squareScale β N : ℝ) ^ 4 ≤ N := by nlinarith only [hD4, hgrowth]
    exact_mod_cast hh
  have hdivisors (n : ℕ) (hnI : n ∈ Ico N (2 * N)) :
      (n.divisors.card : ℝ) * (n + 1).divisors.card ≤ (N : ℝ) ^ (ε / 2) := by
    have hN2 : 2 * N ≤ N ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right N (show 2 ≤ N by omega)
    have hnN : n ≤ N ^ 2 := (mem_Ico.mp hnI).2.le.trans hN2
    have hn1N : n + 1 ≤ N ^ 2 := by have := (mem_Ico.mp hnI).2; omega
    calc
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) :=
        mul_le_mul (hd N (by omega) n hnN) (hd N (by omega) (n + 1) hn1N)
          (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hfinite := finite_lower (H := H) (by omega : 0 < N) hDpos (Real.rpow_nonneg hn.le β)
    hlarge hbudget hdivisors
  have hfactor : 36000 * (N : ℝ) ^ (β - ε / 2) ≤ (N : ℝ) ^ β := by
    simpa only [show (β - ε / 2) + ε / 2 = β by ring] using ha N (by omega)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn (ε / 2))).mp
  calc
    _ = (N : ℝ) ^ (β - ε / 2) := by rw [← Real.rpow_add hn]; congr 1; ring
    _ ≤ (N : ℝ) ^ β / 36000 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 36000)).mpr (by nlinarith only [hfactor])
    _ ≤ (N : ℝ) / (4000 * (squareScale β N : ℝ) ^ 2) := hlower
    _ ≤ _ := hfinite

end PaperP1.TwoSmallKernelLower
