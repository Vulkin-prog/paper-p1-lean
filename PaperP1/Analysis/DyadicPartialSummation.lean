module

public import PaperP1.Analysis.FiniteGramLargeValues
public import Mathlib.Algebra.BigOperators.Intervals
public import PaperP1.Analysis.FiniteAbelNorm

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DyadicPartialSummation
open Finset PaperP1
open scoped Classical

theorem block_partialSum (N k : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) :
    FiniteAbelNorm.partialSum (fun j ↦ a (N+j)) k=
      (∑ n ∈ Icc 1 (N+k-1), a n)-(∑ n ∈ Icc 1 (N-1), a n) := by
  have hblock : FiniteAbelNorm.partialSum (fun j ↦ a (N+j)) k=∑ n ∈ Ico N (N+k), a n := by
    rw [sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left,FiniteAbelNorm.partialSum]
  have h1 : Ico 1 N=Icc 1 (N-1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    congr 1
    omega
  have h2 : Ico 1 (N+k)=Icc 1 (N+k-1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    congr 1
    omega
  have hc := Finset.sum_Ico_consecutive a hN (show N ≤ N+k by omega)
  rw [h1,h2,← hblock] at hc
  calc
    _ = (∑ n ∈ Icc 1 (N-1), a n)+FiniteAbelNorm.partialSum (fun j ↦ a (N+j)) k-
        (∑ n ∈ Icc 1 (N-1), a n) := by abel
    _ = _ := by rw [hc]

theorem weighted_interval_bound (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (hMN : M ≤ 2*N) (a : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hpartial : ∀ M : ℕ, N-1 ≤ M → M ≤ 2*N → ‖∑ n ∈ Icc 1 M, a n‖ ≤ ε*(M : ℝ)) :
    ‖∑ n ∈ Ico N M, a n/(n : ℂ)‖ ≤ 4*ε := by
  let b := fun j : ℕ ↦ a (N+j)
  have hb : ∀ k ≤ M-N, ‖FiniteAbelNorm.partialSum b k‖ ≤ 4*ε*(N : ℝ) := by
    intro k hk
    have hkN : k ≤ N := by omega
    rw [block_partialSum N k hN a]
    have h1 := hpartial (N+k-1) (by omega) (by omega)
    have h0 := hpartial (N-1) le_rfl (by omega)
    have ht := norm_sub_le (∑ n ∈ Icc 1 (N+k-1), a n) (∑ n ∈ Icc 1 (N-1), a n)
    have hscale : (((N+k-1 : ℕ) : ℝ)+((N-1 : ℕ) : ℝ)) ≤ 4*(N : ℝ) := by
      exact_mod_cast (show (N+k-1)+(N-1) ≤ 4*N by omega)
    have hm := mul_le_mul_of_nonneg_left hscale hε
    nlinarith only [h1,h0,ht,hm]
  have hh := FiniteAbelNorm.reciprocal_norm_bound N (M-N) (by omega) b (4*ε*(N : ℝ)) hb
  have he : (∑ n ∈ Ico N M, a n/(n : ℂ))=∑ j ∈ range (M-N), b j/((N+j : ℕ) : ℂ) := by
    rw [sum_Ico_eq_sum_range]
  rw [he]
  exact hh.trans_eq (by
    have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp [hNp])

theorem weighted_block_bound (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hpartial : ∀ M : ℕ, N-1 ≤ M → M ≤ 2*N → ‖∑ n ∈ Icc 1 M, a n‖ ≤ ε*(M : ℝ)) :
    ‖∑ n ∈ Ico N (2*N), a n/(n : ℂ)‖ ≤ 4*ε :=
  weighted_interval_bound N (2*N) hN (by omega) le_rfl a ε hε hpartial
end PaperP1.DyadicPartialSummation
