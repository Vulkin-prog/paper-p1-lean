module

public import PaperP1.Arithmetic.PrimeProductCensus

/-! # An explicit ordinary reciprocal lower bound with variable product order

The prime-count threshold precedes the degree of the squarefree product.
All roots, floors, product cardinalities and largest-prime weights are literal.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeProductReciprocalLower

open PrimeProductCensus ReciprocalOddPivots

theorem root_scale_lower : ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ N k : ℕ, 2 ≤ N → 1 ≤ k →
    1 ≤ Real.log (N : ℝ) →
    Y₀ ≤ ⌊(N : ℝ) ^ (1 / (k : ℝ))⌋₊ →
    8 * Real.log N ≤ (N : ℝ) ^ (1 / (k : ℝ)) →
    (N : ℝ) / ((8 * Real.log N) ^ k * (N : ℝ) ^ (1 / (k : ℝ))) ≤ primeSum N := by
  obtain ⟨Y₀, hthreshold, hcount⟩ := PolynomialPrimeCover.counting_bounds
  refine ⟨Y₀, hthreshold, ?_⟩
  intro N k hN hk hlog hfloor hscale
  let R := (N : ℝ) ^ (1 / (k : ℝ))
  let Y := ⌊R⌋₊
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hH : 0 < Real.log N := by linarith only [hlog]
  have hR : 2 ≤ R := by change 8 * Real.log N ≤ R at hscale; linarith only [hscale, hlog]
  have hY : 2 ≤ Y := hthreshold.trans hfloor
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hYupper : (Y : ℝ) ≤ R := Nat.floor_le (by positivity)
  have hYhalf : R ≤ 2 * (Y : ℝ) := by
    have hh := Nat.lt_floor_add_one R
    change R < (Y : ℝ) + 1 at hh
    linarith only [hh, hR]
  have hrootpow : R ^ k = (N : ℝ) := by
    simpa only [R, one_div] using (Real.rpow_inv_natCast_pow (n := k) hn.le (by omega))
  have hheight : Y ^ k ≤ N := by
    exact_mod_cast (pow_le_pow_left₀ (Nat.cast_nonneg Y) hYupper k).trans_eq hrootpow
  have hYlog : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogupper : (k : ℝ) * Real.log (Y : ℝ) ≤ Real.log N := by
    have hh := Real.log_le_log hYpos hYupper
    dsimp only [R] at hh
    rw [Real.log_rpow hn] at hh
    have hm := mul_le_mul_of_nonneg_left hh hkpos.le
    have hid : (k : ℝ) * (1 / (k : ℝ) * Real.log N) = Real.log N := by field_simp
    rw [hid] at hm
    exact hm
  let q : ℝ := Nat.primeCounting Y
  have hlow := (hcount Y hfloor).1
  have hlowprod : (Y : ℝ) ≤ q * (2 * Real.log Y) :=
    (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hYlog)).mp hlow
  have hmass : (k : ℝ) * R ≤ 4 * Real.log N * q := by
    have h1 := mul_le_mul_of_nonneg_left hYhalf hkpos.le
    have h2 := mul_le_mul_of_nonneg_left hlowprod (by positivity : (0 : ℝ) ≤ 2 * k)
    have h3 := mul_le_mul_of_nonneg_left hlogupper (by positivity : (0 : ℝ) ≤ 4 * q)
    nlinarith only [h1, h2, h3]
  have hmanyR : 2 * (k : ℝ) ≤ q := by
    have hh := mul_le_mul_of_nonneg_left hscale hkpos.le
    change (k : ℝ) * (8 * Real.log N) ≤ (k : ℝ) * R at hh
    nlinarith only [hh, hmass, hH]
  have hmany : 2 * k ≤ Nat.primeCounting Y := by
    dsimp only [q] at hmanyR
    exact_mod_cast hmanyR
  have hbase : R / (8 * Real.log N) ≤ q / (2 * k) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * Real.log N) (by positivity : (0 : ℝ) < 2 * k)).mpr
    nlinarith only [hmass]
  have hchoose : (R / (8 * Real.log N)) ^ k ≤ ((Nat.primeCounting Y).choose k : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hbase k).trans (choose_lower (Nat.primeCounting Y) k hk hmany)
  calc
    _ = (R / (8 * Real.log N)) ^ k / R := by
      rw [div_pow, hrootpow]
      dsimp only [R]
      field_simp
    _ ≤ ((Nat.primeCounting Y).choose k : ℝ) / R :=
      div_le_div_of_nonneg_right hchoose (by positivity)
    _ ≤ ((Nat.primeCounting Y).choose k : ℝ) / Y :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hYpos hYupper
    _ ≤ _ := ordinary_reciprocal_lower N Y k (by omega) hheight

theorem exponential_lower : ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ N k : ℕ, 2 ≤ N → 1 ≤ k →
    1 ≤ Real.log (N : ℝ) →
    Y₀ ≤ ⌊(N : ℝ) ^ (1 / (k : ℝ))⌋₊ →
    8 * Real.log N ≤ (N : ℝ) ^ (1 / (k : ℝ)) →
    (N : ℝ) * Real.exp (-(Real.log N / k + (k : ℝ) * Real.log (8 * Real.log N))) ≤ primeSum N := by
  obtain ⟨Y₀, hY₀, h⟩ := root_scale_lower
  refine ⟨Y₀, hY₀, ?_⟩
  intro N k hN hk hlog hfloor hscale
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : 0 < Real.log N := by linarith only [hlog]
  have hroot : (N : ℝ) ^ (1 / (k : ℝ)) = Real.exp (Real.log N / k) := by
    rw [Real.rpow_def_of_pos hn]
    congr 1
    ring
  have hid : (N : ℝ) * Real.exp (-(Real.log N / k + (k : ℝ) * Real.log (8 * Real.log N))) =
      (N : ℝ) / ((8 * Real.log N) ^ k * (N : ℝ) ^ (1 / (k : ℝ))) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 8 * Real.log N), hroot]
    field_simp
  rw [hid]
  exact h N k hN hk hlog hfloor hscale

end PaperP1.PrimeProductReciprocalLower
