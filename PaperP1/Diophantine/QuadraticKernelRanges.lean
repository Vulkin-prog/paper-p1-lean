module

public import PaperP1.Diophantine.QuadraticKernelFibres
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt

/-! # Actual square-part ranges and positive-integer budgets at real endpoints -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticKernelRanges

open Finset PaperP1.QuadraticKernelFibres

theorem positive_card (W : ℝ) (hW : 0 ≤ W) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ W) : (S.card : ℝ) ≤ W := by
  have hs : S ⊆ Icc 1 ⌊W⌋₊ := by
    intro n hn
    exact mem_Icc.mpr ⟨(hS n hn).1, Nat.le_floor (hS n hn).2⟩
  have hc : S.card ≤ ⌊W⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hs
  exact (by exact_mod_cast hc : (S.card : ℝ) ≤ (⌊W⌋₊ : ℝ)).trans (Nat.floor_le hW)

theorem divisible_card (W : ℝ) (hW : 0 ≤ W) (e : ℕ) (he : 0 < e) (S : Finset ℕ)
    (hS : ∀ q ∈ S, 0 < q ∧ (q : ℝ) ≤ W ∧ e ∣ q) :
    (S.card : ℝ) ≤ W / e := by
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hinj : Set.InjOn (fun q : ℕ ↦ q / e) S := by
    intro q hq r hr heq
    change q / e = r / e at heq
    have hqrec := Nat.div_mul_cancel (hS q hq).2.2
    have hrrec := Nat.div_mul_cancel (hS r hr).2.2
    rw [heq] at hqrec
    omega
  rw [← card_image_of_injOn hinj]
  apply positive_card (W / e) (div_nonneg hW her.le)
  intro k hk
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
  obtain ⟨hqpos, hqW, heq⟩ := hS q hq
  refine ⟨Nat.div_pos (Nat.le_of_dvd hqpos heq) he, ?_⟩
  apply (le_div_iff₀ her).mpr
  have hr : ((q / e : ℕ) : ℝ) * (e : ℝ) = (q : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel heq
  exact hr.le.trans hqW

theorem product_bounds (N h n : ℕ) (_hN : 0 < N) (hlo : N ≤ n)
    (hhi : n ≤ 2 * N) (hh : h ≤ N) :
    N ^ 2 ≤ n * (n + h) ∧ n * (n + h) ≤ 6 * N ^ 2 := by
  constructor
  · nlinarith
  · have hs : n + h ≤ 3 * N := by omega
    have hp := Nat.mul_le_mul hhi hs
    nlinarith

theorem square_part_range (N h n : ℕ) (hN : 0 < N) (hlo : N ≤ n)
    (hhi : n ≤ 2 * N) (hh : h ≤ N) (Q : ℝ) (hQ : 0 < Q)
    (hqlo : Q ≤ kernel h n) (hqhi : (kernel h n : ℝ) ≤ 2 * Q) :
    (N : ℝ) / (2 * Real.sqrt Q) ≤ part h n ∧
      (part h n : ℝ) ≤ 3 * N / Real.sqrt Q := by
  have hn : 0 < n := lt_of_lt_of_le hN hlo
  have hv : (0 : ℝ) < part h n := by exact_mod_cast part_pos h n hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsq := Real.sq_sqrt hQ.le
  have hr : (kernel h n : ℝ) * (part h n : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) + h) := by
    exact_mod_cast representation h n hn
  obtain ⟨hl, hu⟩ := product_bounds N h n hN hlo hhi hh
  have hlr : (N : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + h) := by exact_mod_cast hl
  have hur : (n : ℝ) * ((n : ℝ) + h) ≤ 6 * (N : ℝ) ^ 2 := by exact_mod_cast hu
  have hlow : (N : ℝ) ^ 2 ≤ 2 * Q * (part h n : ℝ) ^ 2 := by nlinarith
  have hupper : Q * (part h n : ℝ) ^ 2 ≤ 6 * (N : ℝ) ^ 2 := by nlinarith
  have hid : (Real.sqrt Q * (part h n : ℝ)) ^ 2 = Q * (part h n : ℝ) ^ 2 := by
    rw [mul_pow, hsq]
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt Q)).mpr
    nlinarith [mul_pos hs hv]
  · apply (le_div_iff₀ hs).mpr
    nlinarith [mul_pos hs hv]

theorem modulus_divides (h n e : ℕ) (hn : 0 < n) (he : e ∣ kernel h n) :
    e * part h n ^ 2 ∣ n * (n + h) := by
  rw [← representation h n hn]
  exact Nat.mul_dvd_mul_right he (part h n ^ 2)

theorem modulus_height (N h n e : ℕ) (hN : 2 ≤ N) (hlo : N ≤ n)
    (hhi : n ≤ 2 * N) (hh : h ≤ N) (he : e ∣ kernel h n) :
    e * part h n ^ 2 ≤ N ^ 5 := by
  have hn : 0 < n := by omega
  have hdiv := Nat.le_of_dvd (Nat.mul_pos hn (by omega)) (modulus_divides h n e hn he)
  have hp := (product_bounds N h n (by omega) hlo hhi hh).2
  have hpow : 6 ≤ N ^ 3 := (by norm_num : 6 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hN 3)
  calc
    _ ≤ 6 * N ^ 2 := hdiv.trans hp
    _ ≤ N ^ 3 * N ^ 2 := Nat.mul_le_mul_right _ hpow
    _ = N ^ 5 := by rw [← pow_add]

end PaperP1.QuadraticKernelRanges
