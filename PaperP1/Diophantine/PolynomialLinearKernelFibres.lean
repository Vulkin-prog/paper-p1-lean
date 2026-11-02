module

public import PaperP1.Diophantine.LinearKernelFibres

/-! # Fixed linear kernels with moving offsets and polynomially bounded positive values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialLinearKernelFibres

open Finset PaperP1.LinearKernelFibres

theorem uniform_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ u v : ℕ, ∀ a b : ℤ, a ≠ b → ∀ S : Finset ℕ,
      (∀ n ∈ S, 0 < (n : ℤ) + a ∧ value n a ≤ N ^ K ∧
        0 < (n : ℤ) + b ∧ value n b ≤ N ^ K ∧
        linearKernel n a = u ∧ linearKernel n b = v) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nq, hNq⟩ := UniformQuadraticCount.positive_count_le_rpow_eventually K ε hε
  refine ⟨max 2 Nq, ?_⟩
  intro N hN u v a b hab S hS
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    have hu : 0 < u := by rw [← (hS n₀ hn₀).2.2.2.2.1]; exact linearKernel_pos n₀ a
    have hv : 0 < v := by rw [← (hS n₀ hn₀).2.2.2.2.2]; exact linearKernel_pos n₀ b
    have huheight : u ≤ N ^ K := by
      rw [← (hS n₀ hn₀).2.2.2.2.1]
      exact (kernel_part_le_value n₀ a (hS n₀ hn₀).1).1.trans (hS n₀ hn₀).2.1
    have hvheight : v ≤ N ^ K := by
      rw [← (hS n₀ hn₀).2.2.2.2.2]
      exact (kernel_part_le_value n₀ b (hS n₀ hn₀).2.2.1).1.trans (hS n₀ hn₀).2.2.2.1
    have hshift : (b - a).natAbs ≤ N ^ K := by
      have haAbs : |(n₀ : ℤ) + a| ≤ (N ^ K : ℕ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (hS n₀ hn₀).2.1
      have hbAbs : |(n₀ : ℤ) + b| ≤ (N ^ K : ℕ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (hS n₀ hn₀).2.2.2.1
      have haUpper := (abs_le.mp haAbs).2
      have hbUpper := (abs_le.mp hbAbs).2
      have hh : |b - a| ≤ (N ^ K : ℕ) := abs_le.mpr ⟨by
        have hp := (hS n₀ hn₀).1
        have hq := (hS n₀ hn₀).2.2.1
        omega, by
        have hp := (hS n₀ hn₀).1
        have hq := (hS n₀ hn₀).2.2.1
        omega⟩
      rw [Int.abs_eq_natAbs] at hh
      exact_mod_cast hh
    have hinj : Set.InjOn (embed a b) S := by
      intro n hn m hm heq
      exact embed_injective_at a b n m v (hS n hn).2.2.1 (hS m hm).2.2.1
        (hS n hn).2.2.2.2.2 (hS m hm).2.2.2.2.2 heq
    rw [← card_image_of_injOn hinj]
    apply hNq N (by omega) v u (N ^ K) (b - a) hv hu (sub_ne_zero.mpr hab.symm)
      hvheight huheight le_rfl hshift
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    have hna := (hS n hn).1
    have hnb := (hS n hn).2.2.1
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · have heq := embed_equation a b n hna hnb
      rwa [(hS n hn).2.2.2.2.1, (hS n hn).2.2.2.2.2] at heq
    · change (squarePart n b : ℤ).natAbs ≤ N ^ K
      simpa only [Int.natAbs_natCast] using
        (kernel_part_le_value n b hnb).2.trans (hS n hn).2.2.2.1
    · change (squarePart n a : ℤ).natAbs ≤ N ^ K
      simpa only [Int.natAbs_natCast] using
        (kernel_part_le_value n a hna).2.trans (hS n hn).2.1
    · change (0 : ℤ) < (squarePart n b : ℕ)
      exact_mod_cast squarePart_pos n b hnb
    · change (0 : ℤ) < (squarePart n a : ℕ)
      exact_mod_cast squarePart_pos n a hna
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

end PaperP1.PolynomialLinearKernelFibres
