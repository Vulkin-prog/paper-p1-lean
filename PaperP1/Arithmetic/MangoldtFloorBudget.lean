module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # An actual factorial floor identity and the first weighted Mangoldt estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MangoldtFloorBudget

open Finset
open scoped ArithmeticFunction

def weightedMangoldt (N : ℕ) : ℝ := ∑ d ∈ range (N + 1), Λ d / (d : ℝ)

theorem log_eq_bounded_divisor_sum (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    Real.log (n : ℝ) = ∑ d ∈ range (N + 1), if d ∣ n then Λ d else 0 := by
  have hset : (range (N + 1)).filter (fun d ↦ d ∣ n) = n.divisors := by
    apply Finset.ext
    intro d
    rw [mem_filter, mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨_hd, hd⟩
      exact ⟨hd, ne_of_gt hn⟩
    · rintro ⟨hd, _hn⟩
      have hdn := Nat.le_of_dvd hn hd
      exact ⟨by omega, hd⟩
  rw [← sum_filter, hset, ArithmeticFunction.vonMangoldt_sum]

theorem factorial_log_floor_identity (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ d ∈ range (N + 1), ((N / d : ℕ) : ℝ) * Λ d := by
  calc
    _ = ∑ n ∈ range N, Real.log ((n + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (Real.sum_log_add_one_eq_log_factorial N).symm
    _ = ∑ n ∈ range N, ∑ d ∈ range (N + 1), if d ∣ n + 1 then Λ d else 0 := by
      apply sum_congr rfl
      intro n hn
      exact log_eq_bounded_divisor_sum (n + 1) N (by omega) (by have := mem_range.mp hn; omega)
    _ = ∑ d ∈ range (N + 1), ∑ n ∈ range N, if d ∣ n + 1 then Λ d else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d _hd
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, Nat.card_multiples]

theorem division_error (N d : ℕ) :
    0 ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) ∧ (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
  refine ⟨sub_nonneg.mpr Nat.cast_div_le, ?_⟩
  by_cases hd : d = 0
  · subst d
    simp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hnat : N ≤ (N / d + 1) * d := by
    have hm := Nat.mod_lt N hdpos
    have he := Nat.mod_add_div N d
    nlinarith
  have hr : (N : ℝ) ≤ (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast hnat
  have hdp : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdiv : (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := (div_le_iff₀ hdp).mpr hr
  linarith

theorem mangoldt_sum_eq_psi (N : ℕ) : (∑ d ∈ range (N + 1), Λ d) = Chebyshev.psi (N : ℝ) := by
  have hset : range (N + 1) = Icc 0 N := by
    apply Finset.ext
    intro d
    rw [mem_range, mem_Icc]
    omega
  rw [hset, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]

theorem factorial_gap_identity (N : ℕ) :
    (N : ℝ) * weightedMangoldt N - Real.log (N.factorial : ℝ) =
      ∑ d ∈ range (N + 1), Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
  rw [weightedMangoldt, mul_sum, factorial_log_floor_identity, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _hd
  ring

theorem factorial_gap_bounds (N : ℕ) :
    0 ≤ (N : ℝ) * weightedMangoldt N - Real.log (N.factorial : ℝ) ∧
      (N : ℝ) * weightedMangoldt N - Real.log (N.factorial : ℝ) ≤ Chebyshev.psi (N : ℝ) := by
  rw [factorial_gap_identity, ← mangoldt_sum_eq_psi]
  constructor
  · exact sum_nonneg (fun d _hd ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (division_error N d).1)
  · apply sum_le_sum
    intro d _hd
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (division_error N d).2 ArithmeticFunction.vonMangoldt_nonneg

theorem weightedMangoldt_bounds (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) - 1 ≤ weightedMangoldt N ∧
      weightedMangoldt N ≤ Real.log (N : ℝ) + (Real.log 4 + 4) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo : (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    simpa only [Real.sum_log_eq_log_factorial] using Real.le_sum_log_nat N
  have hhi : Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
    simpa only [Nat.floor_natCast, Real.sum_log_eq_log_factorial] using Real.sum_log_le' hNr
  have hgap := factorial_gap_bounds N
  have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  constructor
  · apply (mul_le_mul_iff_right₀ hNp).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hNp).mp
    nlinarith

end PaperP1.MangoldtFloorBudget
