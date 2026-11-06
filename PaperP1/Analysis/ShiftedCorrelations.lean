module

public import Mathlib.Data.Nat.Dist
public import PaperP1.Analysis.FiniteDifferencing

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ShiftedCorrelations
open Finset PaperP1
open scoped Classical

def correlation (N : ℕ) (a : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ range (N-d), a n*star (a (n+d))

theorem shifted_correlation (N H h k : ℕ) (hk : k < H) (hle : k ≤ h) (a : ℕ → ℂ) :
    (∑ n ∈ range (N+H), FiniteDifferencing.shifted N a h n*star (FiniteDifferencing.shifted N a k n))=
      correlation N a (h-k) := by
  have he (n : ℕ) : FiniteDifferencing.shifted N a h n*star (FiniteDifferencing.shifted N a k n)=
      if h ≤ n ∧ n < N+k then a (n-h)*star (a (n-k)) else 0 := by
    by_cases hn : h ≤ n ∧ n < N+k
    · have hh' : h ≤ n ∧ n < N+h := by omega
      have hk' : k ≤ n ∧ n < N+k := by omega
      simp only [FiniteDifferencing.shifted,ite_eq_left hh',ite_eq_left hk',ite_eq_left hn]
    · by_cases hh' : h ≤ n ∧ n < N+h
      · have hk' : ¬(k ≤ n ∧ n < N+k) := by omega
        simp only [FiniteDifferencing.shifted,ite_eq_left hh',ite_eq_right hk',ite_eq_right hn,star_zero,mul_zero]
      · simp only [FiniteDifferencing.shifted,ite_eq_right hh',ite_eq_right hn,zero_mul]
  simp_rw [he]
  rw [← sum_filter]
  have hset : (range (N+H)).filter (fun n ↦ h ≤ n ∧ n < N+k)=Ico h (N+k) := by
    ext n
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hset,sum_Ico_eq_sum_range]
  have hlen : N+k-h=N-(h-k) := by omega
  rw [hlen]
  unfold correlation
  apply sum_congr rfl
  intro n hn
  have hsub : h+n-k=n+(h-k) := by omega
  simp only [Nat.add_sub_cancel_left,hsub]

theorem shifted_norm_symm (N H h k : ℕ) (a : ℕ → ℂ) :
    ‖∑ n ∈ range (N+H), FiniteDifferencing.shifted N a h n*star (FiniteDifferencing.shifted N a k n)‖=
    ‖∑ n ∈ range (N+H), FiniteDifferencing.shifted N a k n*star (FiniteDifferencing.shifted N a h n)‖ :=
  FiniteGramLargeValues.gram_norm_symm (range (N+H)) (fun j n ↦ FiniteDifferencing.shifted N a j n) h k

theorem shifted_norm_eq (N H h k : ℕ) (hh : h < H) (hk : k < H) (a : ℕ → ℂ) :
    ‖∑ n ∈ range (N+H), FiniteDifferencing.shifted N a h n*star (FiniteDifferencing.shifted N a k n)‖=
      ‖correlation N a (Nat.dist h k)‖ := by
  rcases le_total k h with hle | hle
  · rw [Nat.dist_eq_sub_of_le_right hle,shifted_correlation N H h k hk hle a]
  · rw [Nat.dist_eq_sub_of_le hle,shifted_norm_symm N H h k a,shifted_correlation N H k h hh hle a]

theorem zero_correlation (N : ℕ) (a : ℕ → ℂ) :
    correlation N a 0=((∑ n ∈ range N, ‖a n‖^2 : ℝ) : ℂ) := by
  rw [correlation,Nat.sub_zero,Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  rw [Nat.add_zero,Complex.ofReal_pow,← Complex.mul_conj']
  rfl

theorem zero_correlation_norm (N : ℕ) (a : ℕ → ℂ) :
    ‖correlation N a 0‖=∑ n ∈ range N, ‖a n‖^2 := by
  rw [zero_correlation,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun _n _hn ↦ sq_nonneg _))]

theorem differencing_bound (N H : ℕ) (hH : 0 < H) (a : ℕ → ℂ) :
    ‖∑ n ∈ range N, a n‖^2 ≤
      (((N+H : ℕ) : ℝ)/(H : ℝ)^2)*(∑ h ∈ range H, ∑ k ∈ range H, ‖correlation N a (Nat.dist h k)‖) := by
  have hh := FiniteDifferencing.normalized_correlation_bound N H hH a
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro h hh
  apply sum_congr rfl
  intro k hk
  exact (shifted_norm_eq N H h k (mem_range.mp hh) (mem_range.mp hk) a).symm
end PaperP1.ShiftedCorrelations
