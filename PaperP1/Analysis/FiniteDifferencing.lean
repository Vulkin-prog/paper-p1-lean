module

public import PaperP1.Analysis.FiniteGramLargeValues
public import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteDifferencing
open Finset PaperP1
open scoped Classical

def shifted {β : Type*} [Zero β] (N : ℕ) (a : ℕ → β) (h n : ℕ) : β :=
  if h ≤ n ∧ n < N+h then a (n-h) else 0

theorem shifted_sum {β : Type*} [AddCommMonoid β] (N H h : ℕ) (hh : h < H) (a : ℕ → β) :
    (∑ n ∈ range (N+H), shifted N a h n)=∑ n ∈ range N, a n := by
  unfold shifted
  rw [← sum_filter]
  have he : (range (N+H)).filter (fun n ↦ h ≤ n ∧ n < N+h)=Ico h (N+h) := by
    ext n
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [he,sum_Ico_eq_sum_range]
  simp

theorem window_sum {β : Type*} [AddCommMonoid β] (N H : ℕ) (a : ℕ → β) :
    (∑ n ∈ range (N+H), ∑ h ∈ range H, shifted N a h n)=H • (∑ n ∈ range N, a n) := by
  rw [sum_comm]
  calc
    _ = ∑ _h ∈ range H, ∑ n ∈ range N, a n :=
      sum_congr rfl (fun h hh ↦ shifted_sum N H h (mem_range.mp hh) a)
    _ = _ := by simp

theorem window_cauchy (N H : ℕ) (a : ℕ → ℂ) :
    (H : ℝ)^2*‖∑ n ∈ range N, a n‖^2 ≤
      ((N+H : ℕ) : ℝ)*(∑ n ∈ range (N+H), ‖∑ h ∈ range H, shifted N a h n‖^2) := by
  have hc := FiniteGramLargeValues.complex_cauchy_square (range (N+H))
    (fun n ↦ ∑ h ∈ range H, shifted N a h n) (fun _n ↦ (1 : ℂ))
  have hcard : (∑ _n ∈ range (N+H), ‖(1 : ℂ)‖^2)=((N+H : ℕ) : ℝ) := by simp
  rw [hcard] at hc
  simp only [mul_one] at hc
  rw [window_sum] at hc
  simp only [nsmul_eq_mul,norm_mul,Complex.norm_natCast,mul_pow] at hc
  simpa only [mul_comm] using hc

theorem window_energy_bound (N H : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ range (N+H), ‖∑ h ∈ range H, shifted N a h n‖^2) ≤
      ∑ h ∈ range H, ∑ k ∈ range H,
        ‖∑ n ∈ range (N+H), shifted N a h n*star (shifted N a k n)‖ := by
  have he := FiniteGramLargeValues.square_expansion (range (N+H)) (range H)
    (fun _h ↦ (1 : ℂ)) (fun h n ↦ shifted N a h n)
  simp only [one_mul,star_one,mul_one,FiniteGramLargeValues.gram] at he
  have hn := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg (fun _n _hn ↦ sq_nonneg _))] at hn
  rw [hn]
  calc
    _ ≤ ∑ h ∈ range H, ‖∑ k ∈ range H, ∑ n ∈ range (N+H), shifted N a h n*star (shifted N a k n)‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum (fun _h _hh ↦ norm_sum_le _ _)

theorem correlation_square_bound (N H : ℕ) (a : ℕ → ℂ) :
    (H : ℝ)^2*‖∑ n ∈ range N, a n‖^2 ≤
      ((N+H : ℕ) : ℝ)*(∑ h ∈ range H, ∑ k ∈ range H,
        ‖∑ n ∈ range (N+H), shifted N a h n*star (shifted N a k n)‖) :=
  (window_cauchy N H a).trans (mul_le_mul_of_nonneg_left (window_energy_bound N H a) (Nat.cast_nonneg _))

theorem normalized_correlation_bound (N H : ℕ) (hH : 0 < H) (a : ℕ → ℂ) :
    ‖∑ n ∈ range N, a n‖^2 ≤
      (((N+H : ℕ) : ℝ)/(H : ℝ)^2)*(∑ h ∈ range H, ∑ k ∈ range H,
        ‖∑ n ∈ range (N+H), shifted N a h n*star (shifted N a k n)‖) := by
  have hh := correlation_square_bound N H a
  have hpos : 0 < (H : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hH)
  calc
    _ ≤ (((N+H : ℕ) : ℝ)*(∑ h ∈ range H, ∑ k ∈ range H,
        ‖∑ n ∈ range (N+H), shifted N a h n*star (shifted N a k n)‖))/(H : ℝ)^2 :=
      (le_div_iff₀ hpos).mpr (by nlinarith only [hh])
    _ = _ := by ring
end PaperP1.FiniteDifferencing
