module

public import PaperP1.Arithmetic.SquareDivisibilityFibres
public import PaperP1.Arithmetic.SquarefreeKernelProducts
public import PaperP1.Arithmetic.KernelSquareBudget

/-! # Actual canonical square parts in the two-small-kernel count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelSquareParts

open Finset PaperP1.DefectivePredicate PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel

def code (h n : ℕ) : ℕ × ℕ := (canonicalSquarePart n, canonicalSquarePart (n + h))

theorem decomposition (H n : ℕ) (hn : 0 < n) :
    smallOddPart H n * canonicalSquarePart n ^ 2 * largeOddKernel H n = n := by
  calc
    _ = (smallOddPart H n * largeOddKernel H n) * canonicalSquarePart n ^ 2 := by ring
    _ = n := by rw [small_mul_large, squarefreeKernel_mul_squarePart hn.ne']

theorem square_part_le (n : ℕ) (hn : 0 < n) : canonicalSquarePart n ≤ n := by
  have hd : 0 < canonicalSquarePart n := Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero n hn.ne')
  have hh := KernelSquareBudget.kernel_square_le 0 n hn
  have hk := largeOddKernel_pos 0 n
  nlinarith only [hh, hk, hd]

theorem fixed_smooth_parts (H h c₁ c₂ : ℕ) (hh : 0 < h) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (N T : ℝ) (hN : 0 < N) (hT : 0 < T) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ N / 2 ≤ n ∧ (n : ℝ) ≤ 3 * N ∧
      smallOddPart H n = c₁ ∧ smallOddPart H (n + h) = c₂ ∧
      (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T) :
    (S.card : ℝ) ≤ 24 * h * T + (S.image (code h)).card := by
  have hfinite := SquareDivisibilityFibres.finite_count c₁ c₂ h hc₁ hc₂ hh (3 * N) (N / (2 * T))
    (by positivity) (by positivity) S (code h) (by
      intro n hn
      obtain ⟨hnpos, hnlo, hnhi, hpart₁, hpart₂, hk₁, hk₂⟩ := hS n hn
      have hmpos : 0 < n + h := by omega
      have hrep₁ := decomposition H n hnpos
      have hrep₂ := decomposition H (n + h) hmpos
      rw [hpart₁] at hrep₁
      rw [hpart₂] at hrep₂
      have hreal₁ : (c₁ : ℝ) * (canonicalSquarePart n : ℝ) ^ 2 * largeOddKernel H n = n := by exact_mod_cast hrep₁
      have hreal₂ : (c₂ : ℝ) * (canonicalSquarePart (n + h) : ℝ) ^ 2 * largeOddKernel H (n + h) = (n + h : ℕ) := by exact_mod_cast hrep₂
      have hmul₁ := mul_le_mul_of_nonneg_left hk₁ (by positivity : (0 : ℝ) ≤ (c₁ : ℝ) * (canonicalSquarePart n : ℝ) ^ 2)
      have hmul₂ := mul_le_mul_of_nonneg_left hk₂ (by positivity : (0 : ℝ) ≤ (c₂ : ℝ) * (canonicalSquarePart (n + h) : ℝ) ^ 2)
      refine ⟨hnpos, hnhi,
        Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero n hnpos.ne'),
        Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero (n + h) hmpos.ne'),
        ⟨largeOddKernel H n, hrep₁.symm⟩, ⟨largeOddKernel H (n + h), hrep₂.symm⟩, ?_, ?_⟩
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T)).mpr
        change N ≤ (c₁ : ℝ) * (canonicalSquarePart n : ℝ) ^ 2 * (2 * T)
        nlinarith only [hnlo, hreal₁, hmul₁]
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T)).mpr
        change N ≤ (c₂ : ℝ) * (canonicalSquarePart (n + h) : ℝ) ^ 2 * (2 * T)
        have hnm : (n : ℝ) ≤ (n + h : ℕ) := by exact_mod_cast Nat.le_add_right n h
        nlinarith only [hnlo, hnm, hreal₂, hmul₂])
  convert hfinite using 1
  field_simp
  ring

theorem product_square_budget (H n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (largeOddKernel H n * largeOddKernel H m) *
      (canonicalSquarePart n * canonicalSquarePart m) ^ 2 ≤ n * m := by
  have hh := Nat.mul_le_mul (KernelSquareBudget.kernel_square_le H n hn) (KernelSquareBudget.kernel_square_le H m hm)
  nlinarith only [hh]

theorem large_square_product (H n m : ℕ) (P X Q : ℝ) (hP : 0 < P) (hX : 0 ≤ X)
    (hn : 0 < n) (hm : 0 < m) (hnX : (n : ℝ) ≤ X) (hmX : (m : ℝ) ≤ X)
    (hparts : P ≤ (canonicalSquarePart n : ℝ) * canonicalSquarePart m)
    (hbudget : X ^ 2 ≤ Q * P ^ 2) :
    (largeOddKernel H n : ℝ) * largeOddKernel H m ≤ Q := by
  have hbase : ((largeOddKernel H n : ℝ) * largeOddKernel H m) *
      ((canonicalSquarePart n : ℝ) * canonicalSquarePart m) ^ 2 ≤ (n : ℝ) * m := by
    exact_mod_cast product_square_budget H n m hn hm
  have hh := mul_le_mul hnX hmX (Nat.cast_nonneg m) hX
  have hsq := pow_le_pow_left₀ hP.le hparts 2
  have hmul := mul_le_mul_of_nonneg_left hsq
    (by positivity : (0 : ℝ) ≤ (largeOddKernel H n : ℝ) * largeOddKernel H m)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hP)).mp
  nlinarith only [hbase, hh, hmul, hbudget]

end PaperP1.TwoSmallKernelSquareParts
