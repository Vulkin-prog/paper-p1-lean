module

public import PaperP1.Analysis.FiniteAbelNorm
public import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteDyadicAssembly
open Finset PaperP1
open scoped Classical

def anchor (N j : ℕ) : ℕ := 2^j*N

theorem anchor_zero (N : ℕ) : anchor N 0=N := by simp [anchor]

theorem anchor_succ (N j : ℕ) : anchor N (j+1)=2*anchor N j := by unfold anchor; rw [pow_succ]; ring

theorem anchor_lower (N j : ℕ) : N ≤ anchor N j := by
  have hh := Nat.mul_le_mul_right N (show 1 ≤ (2 : ℕ)^j from one_le_pow₀ (by decide))
  simpa only [one_mul,anchor] using hh

theorem anchor_mono (N : ℕ) : Monotone (anchor N) := by
  intro j k hjk
  exact Nat.mul_le_mul_right N (Nat.pow_le_pow_right (by decide) hjk)

theorem partition (N M K : ℕ) (hNM : N ≤ M) (a : ℕ → ℂ) :
    (∑ n ∈ Ico N (min M (anchor N K)), a n)=
      ∑ j ∈ range K, ∑ n ∈ Ico (min M (anchor N j)) (min M (anchor N (j+1))), a n := by
  induction K with
  | zero => simp [anchor,hNM]
  | succ K ih =>
    have hStart : N ≤ min M (anchor N K) := le_min hNM (anchor_lower N K)
    have hNext : min M (anchor N K) ≤ min M (anchor N (K+1)) := by
      apply min_le_min_left M
      rw [anchor_succ]
      omega
    have hh := sum_Ico_consecutive a hStart hNext
    rw [sum_range_succ,← ih]
    exact hh.symm

theorem norm_bound (N M K : ℕ) (hNM : N ≤ M) (hCover : M ≤ anchor N K)
    (a : ℕ → ℂ) (D : ℕ → ℝ) (hD : ∀ j < K, 0 ≤ D j)
    (hBlocks : ∀ j < K, ∀ U, anchor N j ≤ U → U ≤ 2*anchor N j →
      ‖∑ n ∈ Ico (anchor N j) U, a n‖ ≤ D j) :
    ‖∑ n ∈ Ico N M, a n‖ ≤ ∑ j ∈ range K, D j := by
  have hSplit := partition N M K hNM a
  rw [min_eq_left hCover] at hSplit
  rw [hSplit]
  calc
    _ ≤ ∑ j ∈ range K, ‖∑ n ∈ Ico (min M (anchor N j)) (min M (anchor N (j+1))), a n‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have hjK := mem_range.mp hj
      by_cases hCase : anchor N j ≤ M
      · rw [min_eq_right hCase]
        apply hBlocks j hjK
        · exact le_min hCase (by rw [anchor_succ]; omega)
        · exact (min_le_right _ _).trans_eq (anchor_succ N j)
      · have hM : M ≤ anchor N j := by omega
        have hM' : M ≤ anchor N (j+1) := by rw [anchor_succ]; omega
        rw [min_eq_left hM,min_eq_left hM']
        simpa only [Ico_self,sum_empty,norm_zero] using hD j hjK

theorem constant_norm_bound (N M K : ℕ) (hNM : N ≤ M) (hCover : M ≤ anchor N K)
    (a : ℕ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hBlocks : ∀ j < K, ∀ U, anchor N j ≤ U → U ≤ 2*anchor N j →
      ‖∑ n ∈ Ico (anchor N j) U, a n‖ ≤ D) :
    ‖∑ n ∈ Ico N M, a n‖ ≤ (K : ℝ)*D := by
  have hh := norm_bound N M K hNM hCover a (fun _ ↦ D) (fun _ _ ↦ hD) hBlocks
  simpa only [sum_const,card_range,nsmul_eq_mul] using hh
end PaperP1.FiniteDyadicAssembly
