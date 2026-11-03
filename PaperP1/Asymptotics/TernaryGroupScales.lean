module

public import PaperP1.Arithmetic.TernaryGroupCounts
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Uniform critical-window scales for the actual ternary CRT covers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryGroupScales

open Finset PaperP1.CriticalBandScale

theorem radius_length_factor (C : ℝ) (D : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (d e : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      c * (2 * R + 1 : ℕ) ^ d * ((L + 1 : ℕ) : ℝ) ^ e ≤ (N : ℝ) ^ ε := by
  obtain ⟨NS, hs⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (c * (2 * D + 1 : ℕ) ^ d) (d + e) ε hε
  refine ⟨max 2 (max NS NP), by omega, ?_⟩
  intro N hN L R hband hR
  have hB := (hs N (by omega) L hband).2
  have hbase : 2 * R + 1 ≤ (2 * D + 1) * (L + 1) := by nlinarith
  have hbaser : ((2 * R + 1 : ℕ) : ℝ) ≤ (2 * D + 1 : ℕ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hbase
  have hbound := hp N (by omega) L hB
  rw [abs_of_nonneg (by positivity : 0 ≤ c * (2 * D + 1 : ℕ) ^ d * (L + 1 : ℝ) ^ (d + e))] at hbound
  calc
    _ ≤ c * ((2 * D + 1 : ℕ) * ((L + 1 : ℕ) : ℝ)) ^ d * ((L + 1 : ℕ) : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hbaser d) hc) (by positivity)
    _ = c * (2 * D + 1 : ℕ) ^ d * (L + 1 : ℝ) ^ (d + e) := by
      rw [mul_pow, pow_add]
      push_cast
      ring
    _ ≤ _ := hbound

theorem affine_power_bound (a R d : ℕ) : a * R ^ d + 1 ≤ (a + 1) * (2 * R + 1) ^ d := by
  have hr : R ^ d ≤ (2 * R + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have h1 : 1 ≤ (2 * R + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem plane_pool_factor_bound (R : ℕ) :
    (TernaryOffsetPlanes.planePool R).card * (2 * R + 1) ^ 6 ≤
      (17 ^ 3 * 49) * (2 * R + 1) ^ 15 := by
  have h2 := affine_power_bound 16 R 2
  have h3 := affine_power_bound 48 R 3
  rw [TernaryOffsetPlanes.planePool_card]
  calc
    _ ≤ (17 * (2 * R + 1) ^ 2) ^ 3 * (49 * (2 * R + 1) ^ 3) * (2 * R + 1) ^ 6 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left h2 3) h3)
    _ = _ := by ring

theorem plane_length_factor (C : ℝ) (D : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (e : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      c * ((TernaryOffsetPlanes.planePool R).card : ℝ) * (2 * R + 1 : ℕ) ^ 6 *
        ((L + 1 : ℕ) : ℝ) ^ e ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, hp⟩ := radius_length_factor C D (c * (17 ^ 3 * 49 : ℕ)) (by positivity) 15 e ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR
  have hplane : ((TernaryOffsetPlanes.planePool R).card : ℝ) * (2 * R + 1 : ℕ) ^ 6 ≤
      (17 ^ 3 * 49 : ℕ) * (2 * R + 1 : ℕ) ^ 15 := by exact_mod_cast plane_pool_factor_bound R
  calc
    _ = c * (((TernaryOffsetPlanes.planePool R).card : ℝ) * (2 * R + 1 : ℕ) ^ 6) *
        ((L + 1 : ℕ) : ℝ) ^ e := by ring
    _ ≤ c * ((17 ^ 3 * 49 : ℕ) * (2 * R + 1 : ℕ) ^ 15) * ((L + 1 : ℕ) : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hplane hc) (by positivity)
    _ = (c * (17 ^ 3 * 49 : ℕ)) * (2 * R + 1 : ℕ) ^ 15 * ((L + 1 : ℕ) : ℝ) ^ e := by ring
    _ ≤ _ := hp N hN L R hband hR

theorem forcing_scale (C : ℝ) (D : ℕ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      (6 * (D * N) * H ^ 2 : ℕ) < (N : ℝ) ^ (6 / 5 : ℝ) ∧
        2 * (D * N) * (H + 1) ≤ N ^ 2 := by
  obtain ⟨NS, hs⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (6 * (D : ℝ) ^ 3) 2 (1 / 10) (by norm_num)
  obtain ⟨NQ, hq⟩ := CriticalPolynomialScale.polynomial_lt_scale C
    (2 * (D : ℝ) * (D + 1)) (by positivity) 1
  refine ⟨max 2 (max NS (max NP NQ)), by omega, ?_⟩
  intro N hN L H hband hH
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hHr : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hH
  push_cast at hHr
  have hpoly := hp N (by omega) L hB
  rw [abs_of_nonneg (by positivity : 0 ≤ 6 * (D : ℝ) ^ 3 * (L + 1 : ℝ) ^ 2)] at hpoly
  have hsmall : (6 * (D * N) * H ^ 2 : ℕ) ≤ (N : ℝ) ^ (11 / 10 : ℝ) := by
    calc
      _ ≤ (6 * (D : ℝ) ^ 3 * ((L + 1 : ℕ) : ℝ) ^ 2) * N := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hHr 2)
          (by positivity : 0 ≤ 6 * (D : ℝ) * N)]
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * N :=
        mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add, Nat.cast_one] using hpoly) (Nat.cast_nonneg N)
      _ = (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (by linarith : 0 < (N : ℝ))]; congr 1; norm_num
  have hquad : (2 * (D * N) * (H + 1) : ℕ) ≤ N ^ 2 := by
    have hpq := hq N (by omega) L hband
    have hqreal : (2 * (D * N) * (H + 1) : ℕ) < (N : ℝ) ^ 2 := by
      have hb1 : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L + 1)
      have hlin : (2 * D * (H + 1) : ℕ) < (N : ℝ) := by
        push_cast at hpq hHr hb1 ⊢
        simp only [pow_one] at hpq
        nlinarith [mul_nonneg (Nat.cast_nonneg D) (sub_nonneg.mpr hb1)]
      have hmul := mul_lt_mul_of_pos_right hlin (by linarith : (0 : ℝ) < N)
      push_cast at hmul ⊢
      nlinarith
    exact_mod_cast hqreal.le
  exact ⟨hsmall.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hn (by norm_num)), hquad⟩

def logConstant : ℝ := Real.log 2 + 4 / (5 * lowerScale)

theorem logConstant_nonneg : 0 ≤ logConstant := by
  unfold logConstant
  exact add_nonneg (Real.log_nonneg (by norm_num)) (div_nonneg (by norm_num) (mul_pos (by norm_num) lowerScale_pos).le)

theorem pair_threshold_log (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Real.log (2 * (N : ℝ) ^ (4 / 5 : ℝ)) ≤ logConstant * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨NS, hs⟩ := critical_band_scale C
  refine ⟨max 2 NS, by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlow := (hs N (by omega) L hband).1
  have hb : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L + 1)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hn _).ne', Real.log_rpow hn]
  have hlog : Real.log N ≤ ((L + 1 : ℕ) : ℝ) / lowerScale := (le_div_iff₀ lowerScale_pos).mpr (by nlinarith)
  unfold logConstant
  have h2 := mul_le_mul_of_nonneg_left hb (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have h4 := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 4 / 5)
  calc
    _ ≤ Real.log 2 * ((L + 1 : ℕ) : ℝ) + (4 / 5 : ℝ) * (((L + 1 : ℕ) : ℝ) / lowerScale) :=
      add_le_add (by simpa only [mul_one] using h2) h4
    _ = _ := by ring

end PaperP1.TernaryGroupScales
