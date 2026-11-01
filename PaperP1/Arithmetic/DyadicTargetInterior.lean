module

public import PaperP1.Arithmetic.NormalizedPairGeometry
public import Mathlib.Tactic.Linarith

/-! # A finite integer separation of interior target fractions and dyadic endpoints -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.DyadicTargetInterior

open PaperP1.Arithmetic

theorem scaled_abs_bound {v : ℤ} {m B H : ℕ} (hm : 1 ≤ m)
    (hlo : -(B : ℤ) ≤ v) (hhi : (m : ℤ) * v ≤ H) : |v| ≤ (B : ℤ) + H := by
  have hmZ : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hB0 : (0 : ℤ) ≤ B := Nat.cast_nonneg B
  have hH0 : (0 : ℤ) ≤ H := Nat.cast_nonneg H
  apply abs_le.mpr
  constructor
  · linarith only [hlo, hH0]
  · by_cases hv : 0 ≤ v
    · have hmul := mul_le_mul_of_nonneg_right hmZ hv
      nlinarith only [hmul, hhi, hB0]
    · linarith only [hv, hB0, hH0]

theorem weak_ratio_bounds {a b c d t N z B H : ℕ} {h : ℤ}
    (hsrcA : (N : ℤ) - B ≤ (a : ℤ) * t) (hsrcB : (b : ℤ) * t ≤ 2 * N + B)
    (hNz : N ≤ z) (hzN : z ≤ 2 * N) (hdH : d ≤ H) (hh : |h| ≤ H)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) (ht : 2 * H * (B + 1) < t) :
    b * d ≤ 2 * c ∧ c ≤ 2 * a * d := by
  have hd0 : (0 : ℤ) ≤ d := Nat.cast_nonneg d
  have ht0 : (0 : ℤ) ≤ t := Nat.cast_nonneg t
  have hHB0 : (0 : ℤ) ≤ (H : ℤ) * B := mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg B)
  have hbig : (2 : ℤ) * H * (B + 1) < t := by exact_mod_cast ht
  have hdHZ : (d : ℤ) ≤ H := by exact_mod_cast hdH
  have hDB := mul_le_mul_of_nonneg_right hdHZ (Nat.cast_nonneg (α := ℤ) B)
  have hNzZ : (N : ℤ) ≤ z := by exact_mod_cast hNz
  have hzNZ : (z : ℤ) ≤ 2 * N := by exact_mod_cast hzN
  obtain ⟨hhlo, hhhi⟩ := abs_le.mp hh
  constructor
  · by_contra hnot
    have hgt : (2 : ℤ) * c < (b : ℤ) * d := by exact_mod_cast (show 2 * c < b * d by omega)
    have hgap : (1 : ℤ) ≤ (b : ℤ) * d - 2 * c := by omega
    have hmul := mul_le_mul_of_nonneg_right hgap ht0
    have hsource := mul_le_mul_of_nonneg_left hsrcB hd0
    have htargetLo := mul_le_mul_of_nonneg_left hNzZ hd0
    nlinarith only [hmul, hsource, htargetLo, htarget, hDB, hhhi, hbig, hHB0]
  · by_contra hnot
    have hgt : (2 : ℤ) * a * d < (c : ℤ) := by exact_mod_cast (show 2 * a * d < c by omega)
    have hgap : (1 : ℤ) ≤ (c : ℤ) - 2 * a * d := by omega
    have hmul := mul_le_mul_of_nonneg_right hgap ht0
    have hsource := mul_le_mul_of_nonneg_left hsrcA (show 0 ≤ (2 : ℤ) * d by positivity)
    have htargetHi := mul_le_mul_of_nonneg_left hzNZ hd0
    nlinarith only [hmul, hsource, htargetHi, htarget, hDB, hhlo, hbig, Nat.cast_nonneg (α := ℤ) H]

theorem lower_endpoint {b c d t N z B H : ℕ} {h : ℤ} (hd : 0 < d)
    (hsrcB : (b : ℤ) * t ≤ 2 * N + B) (hNz : N ≤ z) (hh : |h| ≤ H)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) (hbd : b * d = 2 * c) :
    |(b : ℤ) * t - 2 * N| ≤ (B : ℤ) + 2 * H := by
  have hNzZ : (N : ℤ) ≤ z := by exact_mod_cast hNz
  have htargetLo := mul_le_mul_of_nonneg_left hNzZ (Nat.cast_nonneg (α := ℤ) d)
  have heq : (b : ℤ) * d = 2 * c := by exact_mod_cast hbd
  have heqMul := congrArg (fun v : ℤ ↦ v * t) heq
  have hscale : (d : ℤ) * (2 * N - (b : ℤ) * t) ≤ (2 * H : ℕ) := by
    have hhhi := (abs_le.mp hh).2
    push_cast
    nlinarith only [htargetLo, htarget, heqMul, hhhi]
  have hlo : -(B : ℤ) ≤ 2 * N - (b : ℤ) * t := by linarith only [hsrcB]
  have hbound := scaled_abs_bound (show 1 ≤ d by omega) hlo hscale
  rw [abs_sub_comm] at hbound
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem upper_endpoint {a c d t N z B H : ℕ} {h : ℤ} (hd : 0 < d)
    (hsrcA : (N : ℤ) - B ≤ (a : ℤ) * t) (hzN : z ≤ 2 * N) (hh : |h| ≤ H)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) (hca : c = 2 * a * d) :
    |(a : ℤ) * t - N| ≤ (B : ℤ) + H := by
  have hzNZ : (z : ℤ) ≤ 2 * N := by exact_mod_cast hzN
  have htargetHi := mul_le_mul_of_nonneg_left hzNZ (Nat.cast_nonneg (α := ℤ) d)
  have heq : (c : ℤ) = 2 * a * d := by exact_mod_cast hca
  have heqMul := congrArg (fun v : ℤ ↦ v * t) heq
  have hscale : ((2 * d : ℕ) : ℤ) * ((a : ℤ) * t - N) ≤ H := by
    have hhlo := (abs_le.mp hh).1
    push_cast
    nlinarith only [htargetHi, htarget, heqMul, hhlo]
  have hlo : -(B : ℤ) ≤ (a : ℤ) * t - N := by linarith only [hsrcA]
  exact scaled_abs_bound (show 1 ≤ 2 * d by omega) hlo hscale

theorem strict_interior_of_no_endpoints {a b c d t N z B H : ℕ} {h : ℤ} (hd : 0 < d)
    (hsrcA : (N : ℤ) - B ≤ (a : ℤ) * t) (hsrcB : (b : ℤ) * t ≤ 2 * N + B)
    (hNz : N ≤ z) (hzN : z ≤ 2 * N) (hdH : d ≤ H) (hh : |h| ≤ H)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) (ht : 2 * H * (B + 1) < t)
    (hawayA : (B : ℤ) + 2 * H < |(a : ℤ) * t - N|)
    (hawayB : (B : ℤ) + 2 * H < |(b : ℤ) * t - 2 * N|) :
    b * d < 2 * c ∧ c < 2 * a * d := by
  obtain ⟨hlo, hhi⟩ := weak_ratio_bounds hsrcA hsrcB hNz hzN hdH hh htarget ht
  have hneLo : b * d ≠ 2 * c := by
    intro heq
    have hbound := lower_endpoint hd hsrcB hNz hh htarget heq
    omega
  have hneHi : c ≠ 2 * a * d := by
    intro heq
    have hbound := upper_endpoint hd hsrcA hzN hh htarget heq
    have hH0 : (0 : ℤ) ≤ H := Nat.cast_nonneg H
    omega
  omega

end PaperP1.DyadicTargetInterior
