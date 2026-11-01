module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Symmetric rational coincidence densities of three integer slopes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleDensity

def pairDensity (a b : ℕ) : ℝ := (Nat.gcd a b : ℝ) / (max a b : ℕ)

def density (a b c : ℕ) : ℝ :=
  pairDensity a b + pairDensity a c + pairDensity b c -
    1 / (max a (max b c) : ℕ)

theorem pairDensity_comm (a b : ℕ) : pairDensity a b = pairDensity b a := by
  simp only [pairDensity, Nat.gcd_comm, max_comm]

theorem density_swap (a b c : ℕ) : density a b c = density b a c := by
  simp only [density, pairDensity_comm a b, max_left_comm]
  ring

theorem density_cycle (a b c : ℕ) : density a b c = density b c a := by
  unfold density
  rw [pairDensity_comm b a, pairDensity_comm c a]
  have hmax : max a (max b c) = max b (max c a) := by omega
  rw [hmax]
  ring

theorem density_ordered {u v w : ℕ} (huv : u ≤ v) (hvw : v ≤ w) :
    density u v w = (Nat.gcd u v : ℝ) / v +
      ((Nat.gcd u w : ℝ) + Nat.gcd v w - 1) / w := by
  simp only [density, pairDensity, max_eq_right huv, max_eq_right hvw,
    max_eq_right (huv.trans hvw)]
  ring

theorem third_window_bound {x y z : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hz : 0 < z) :
    density x y z ≤ (Nat.gcd x y : ℝ) / y +
      ((Nat.gcd x z : ℝ) + Nat.gcd y z - 1) / z := by
  have hy : 0 < y := hx.trans_le hxy
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hgcd : (1 : ℝ) ≤ Nat.gcd y z := by exact_mod_cast (Nat.gcd_pos_of_pos_left z hy)
  by_cases hyz : y ≤ z
  · rw [density_ordered hxy hyz]
  · have hzy : z ≤ y := by omega
    by_cases hxz : x ≤ z
    · simp only [density, pairDensity, max_eq_right hxy, max_eq_right hxz,
        max_eq_left hzy]
      have hterm := div_le_div_of_nonneg_left (by linarith : 0 ≤ (Nat.gcd y z : ℝ) - 1)
        hzR (by exact_mod_cast hzy : (z : ℝ) ≤ y)
      ring_nf at hterm ⊢
      linarith
    · have hzx : z ≤ x := by omega
      simp only [density, pairDensity, max_eq_right hxy, max_eq_left hzx,
        max_eq_left hzy]
      have hxterm := div_le_div_of_nonneg_left (Nat.cast_nonneg (Nat.gcd x z))
        hzR (by exact_mod_cast hzx : (z : ℝ) ≤ x)
      have hyterm := div_le_div_of_nonneg_left (by linarith : 0 ≤ (Nat.gcd y z : ℝ) - 1)
        hzR (by exact_mod_cast hzy : (z : ℝ) ≤ y)
      ring_nf at hxterm hyterm ⊢
      linarith

theorem pairDensity_le_fifth {x y : ℕ} (hxy : 0 < max x y)
    (hheight : 5 * Nat.gcd x y ≤ max x y) : pairDensity x y ≤ 1 / 5 := by
  unfold pairDensity
  apply (div_le_iff₀ (by exact_mod_cast hxy : (0 : ℝ) < (max x y : ℕ))).mpr
  have hR : 5 * (Nat.gcd x y : ℝ) ≤ (max x y : ℕ) := by exact_mod_cast hheight
  linarith

theorem all_pairs_high {u v w : ℕ} (hu : 0 < u) (huv : u < v) (hvw : v < w)
    (h1 : 5 * Nat.gcd u v ≤ v) (h2 : 5 * Nat.gcd u w ≤ w)
    (h3 : 5 * Nat.gcd v w ≤ w) : density u v w ≤ 3 / 5 := by
  have hw : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hsub : 0 ≤ 1 / (w : ℝ) := by positivity
  have huv' := pairDensity_le_fifth (x := u) (y := v) (by omega) (by simpa only [max_eq_right huv.le] using h1)
  have huw' := pairDensity_le_fifth (x := u) (y := w) (by omega) (by simpa only [max_eq_right (by omega : u ≤ w)] using h2)
  have hvw' := pairDensity_le_fifth (x := v) (y := w) (by omega) (by simpa only [max_eq_right hvw.le] using h3)
  unfold density
  rw [show max u (max v w) = w by omega]
  linarith

/-- A pair of reduced height below five has one of just two ratios. -/
theorem small_pair {x y : ℕ} (hx : 0 < x) (hxy : x < y) (hy2x : y < 2 * x)
    (hsmall : y < 5 * Nat.gcd x y) :
    ∃ d : ℕ, 0 < d ∧ ((x = 2 * d ∧ y = 3 * d) ∨ (x = 3 * d ∧ y = 4 * d)) := by
  let d := Nat.gcd x y
  let a := x / d
  let b := y / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left y hx
  have hxa : x = d * a := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)).symm
  have hyb : y = d * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)).symm
  have hcop : Nat.Coprime a b := Nat.gcd_div_gcd_div_gcd_of_pos_left hx
  have ha0 : 0 < a := by nlinarith
  have hab : a < b := by
    exact Nat.lt_of_mul_lt_mul_left (show d * a < d * b by omega)
  have hb2a : b < 2 * a := by
    exact Nat.lt_of_mul_lt_mul_left (show d * b < d * (2 * a) by nlinarith)
  have hb5 : b < 5 := by
    exact Nat.lt_of_mul_lt_mul_left (show d * b < d * 5 by nlinarith)
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 4 := by omega
  refine ⟨d, hd, ?_⟩
  interval_cases a <;> interval_cases b <;> omega

end PaperP1.RationalTripleDensity
