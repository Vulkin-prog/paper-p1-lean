module

public import PaperP1.Diophantine.QuadraticKernelRanges

/-! # Actual square-part ranges on N/2 <= n <= 3N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WideQuadraticKernelRanges

open PaperP1.QuadraticKernelFibres PaperP1.QuadraticKernelRanges

theorem product_bounds (N h n : ℕ) (hlo : N ≤ 2 * n) (hhi : n ≤ 3 * N) (hh : h ≤ N) :
    N ^ 2 ≤ 4 * (n * (n + h)) ∧ n * (n + h) ≤ 12 * N ^ 2 := by
  constructor
  · nlinarith
  · have hs : n + h ≤ 4 * N := by omega
    have hp := Nat.mul_le_mul hhi hs
    nlinarith

theorem square_part_range (N h n : ℕ) (hN : 0 < N) (hlo : N ≤ 2 * n)
    (hhi : n ≤ 3 * N) (hh : h ≤ N) (Q : ℝ) (hQ : 0 < Q)
    (hqlo : Q ≤ kernel h n) (hqhi : (kernel h n : ℝ) ≤ 2 * Q) :
    (N : ℝ) / (4 * Real.sqrt Q) ≤ part h n ∧
      (part h n : ℝ) ≤ 4 * N / Real.sqrt Q := by
  have hn : 0 < n := by omega
  have hv : (0 : ℝ) < part h n := by exact_mod_cast part_pos h n hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsq := Real.sq_sqrt hQ.le
  have hr : (kernel h n : ℝ) * (part h n : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) + h) := by
    exact_mod_cast representation h n hn
  obtain ⟨hl, hu⟩ := product_bounds N h n hlo hhi hh
  have hlr : (N : ℝ) ^ 2 ≤ 4 * ((n : ℝ) * ((n : ℝ) + h)) := by exact_mod_cast hl
  have hur : (n : ℝ) * ((n : ℝ) + h) ≤ 12 * (N : ℝ) ^ 2 := by exact_mod_cast hu
  have hlow : (N : ℝ) ^ 2 ≤ 8 * Q * (part h n : ℝ) ^ 2 := by nlinarith
  have hupper : Q * (part h n : ℝ) ^ 2 ≤ 12 * (N : ℝ) ^ 2 := by nlinarith
  have hid : (Real.sqrt Q * (part h n : ℝ)) ^ 2 = Q * (part h n : ℝ) ^ 2 := by
    rw [mul_pow, hsq]
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt Q)).mpr
    nlinarith [mul_pos hs hv]
  · apply (le_div_iff₀ hs).mpr
    nlinarith [mul_pos hs hv]

theorem modulus_height (N h n e : ℕ) (hN : 2 ≤ N) (hlo : N ≤ 2 * n)
    (hhi : n ≤ 3 * N) (hh : h ≤ N) (he : e ∣ kernel h n) :
    e * part h n ^ 2 ≤ N ^ 6 := by
  have hn : 0 < n := by omega
  have hdiv := Nat.le_of_dvd (Nat.mul_pos hn (by omega)) (modulus_divides h n e hn he)
  have hp := (product_bounds N h n hlo hhi hh).2
  have hpow : 12 ≤ N ^ 4 := (by norm_num : 12 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4)
  calc
    _ ≤ 12 * N ^ 2 := hdiv.trans hp
    _ ≤ N ^ 4 * N ^ 2 := Nat.mul_le_mul_right _ hpow
    _ = N ^ 6 := by rw [← pow_add]

end PaperP1.WideQuadraticKernelRanges
