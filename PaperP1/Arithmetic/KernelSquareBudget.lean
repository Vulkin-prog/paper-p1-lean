module

public import PaperP1.Arithmetic.SmallPrimeBudget
public import PaperP1.Arithmetic.TruncatedKernelProducts

/-! # Canonical square parts and the supply of large smooth squarefree parts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KernelSquareBudget

open Finset PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.DefectivePredicate

theorem large_kernel_le_squarefree (H n : ℕ) : largeOddKernel H n ≤ squarefreeKernel n := by
  rw [← small_mul_large H n]
  exact Nat.le_mul_of_pos_left _ (smallOddPart_pos H n)

theorem kernel_square_le (H n : ℕ) (hn : 0 < n) :
    largeOddKernel H n * canonicalSquarePart n ^ 2 ≤ n := by
  calc
    _ ≤ squarefreeKernel n * canonicalSquarePart n ^ 2 :=
      Nat.mul_le_mul_right _ (large_kernel_le_squarefree H n)
    _ = n := squarefreeKernel_mul_squarePart hn.ne'

theorem pair_bound (H n m : ℕ) (L X Q : ℝ) (hL : 0 < L) (hX : 0 ≤ X)
    (hn : 0 < n) (hm : 0 < m) (hnX : (n : ℝ) ≤ X) (hmX : (m : ℝ) ≤ X)
    (hnL : L ≤ (canonicalSquarePart n : ℝ) ^ 2)
    (hmL : L ≤ (canonicalSquarePart m : ℝ) ^ 2)
    (hbudget : X ^ 2 ≤ Q * L ^ 2) :
    (largeOddKernel H n : ℝ) * (largeOddKernel H m : ℝ) ≤ Q := by
  have hkn : (largeOddKernel H n : ℝ) * (canonicalSquarePart n : ℝ) ^ 2 ≤ X := by
    exact (by exact_mod_cast kernel_square_le H n hn :
      (largeOddKernel H n : ℝ) * (canonicalSquarePart n : ℝ) ^ 2 ≤ n).trans hnX
  have hkm : (largeOddKernel H m : ℝ) * (canonicalSquarePart m : ℝ) ^ 2 ≤ X := by
    exact (by exact_mod_cast kernel_square_le H m hm :
      (largeOddKernel H m : ℝ) * (canonicalSquarePart m : ℝ) ^ 2 ≤ m).trans hmX
  have hmul := mul_le_mul hkn hkm (by positivity : (0 : ℝ) ≤
    (largeOddKernel H m : ℝ) * (canonicalSquarePart m : ℝ) ^ 2) hX
  have hparts := mul_le_mul hnL hmL hL.le (sq_nonneg (canonicalSquarePart n : ℝ))
  have hlow := mul_le_mul_of_nonneg_left hparts
    (mul_nonneg (Nat.cast_nonneg (largeOddKernel H n)) (Nat.cast_nonneg (largeOddKernel H m)))
  have hmain : ((largeOddKernel H n : ℝ) * (largeOddKernel H m : ℝ)) * L ^ 2 ≤ Q * L ^ 2 := by
    nlinarith only [hmul, hlow, hbudget]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp hmain

theorem large_squares_card_le_one (S : Finset ℕ) (H : ℕ) (L X Q : ℝ)
    (hL : 0 < L) (hX : 0 ≤ X) (hbudget : X ^ 2 ≤ Q * L ^ 2)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ X)
    (hpairs : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → Q < (largeOddKernel H n : ℝ) * (largeOddKernel H m : ℝ)) :
    (S.filter fun n ↦ L < (canonicalSquarePart n : ℝ) ^ 2).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro n hn m hm
  obtain ⟨hnS, hnL⟩ := mem_filter.mp hn
  obtain ⟨hmS, hmL⟩ := mem_filter.mp hm
  by_contra hne
  exact (not_lt_of_ge (pair_bound H n m L X Q hL hX (hS n hnS).1 (hS m hmS).1
    (hS n hnS).2 (hS m hmS).2 hnL.le hmL.le hbudget)) (hpairs n hnS m hmS hne)

theorem smooth_part_lower (Y n : ℕ) (N a : ℝ) (hN : 0 < N) (hn : 0 < n)
    (hlower : a * N ≤ n)
    (hsquare : (canonicalSquarePart n : ℝ) ^ 2 ≤ N ^ (19 / 25 : ℝ))
    (hkernel : (largeOddKernel Y n : ℝ) ≤ N ^ (1 / 5 : ℝ)) :
    a * N ^ (1 / 25 : ℝ) ≤ smallOddPart Y n := by
  have hrep : (smallOddPart Y n : ℝ) * (largeOddKernel Y n : ℝ) *
      (canonicalSquarePart n : ℝ) ^ 2 = n := by
    exact_mod_cast (by rw [small_mul_large, squarefreeKernel_mul_squarePart hn.ne'] :
      smallOddPart Y n * largeOddKernel Y n * canonicalSquarePart n ^ 2 = n)
  have hparts := mul_le_mul hkernel hsquare (sq_nonneg (canonicalSquarePart n : ℝ))
    (Real.rpow_nonneg hN.le _)
  have hp : (largeOddKernel Y n : ℝ) * (canonicalSquarePart n : ℝ) ^ 2 ≤ N ^ (24 / 25 : ℝ) := by
    convert hparts using 1
    rw [← Real.rpow_add hN]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (smallOddPart Y n))
  have hidentity : a * N = (a * N ^ (1 / 25 : ℝ)) * N ^ (24 / 25 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hN]
    norm_num
  have hbound : (a * N ^ (1 / 25 : ℝ)) * N ^ (24 / 25 : ℝ) ≤
      (smallOddPart Y n : ℝ) * N ^ (24 / 25 : ℝ) := by
    rw [← hidentity]
    exact hlower.trans (by nlinarith only [hrep, hmul])
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hN _)).mp hbound

theorem good_values_card {α : Type*} (S : Finset α) (v : α → ℕ) (Y t k : ℕ) (L K : ℝ)
    (hcard : t + k ≤ S.card)
    (hsquare : (S.filter fun n ↦ L < (canonicalSquarePart (v n) : ℝ) ^ 2).card ≤ 1)
    (hlarge : (S.filter fun n ↦ K < (largeOddKernel Y (v n) : ℝ)).card < t) :
    k ≤ (S.filter fun n ↦ (canonicalSquarePart (v n) : ℝ) ^ 2 ≤ L ∧ (largeOddKernel Y (v n) : ℝ) ≤ K).card := by
  classical
  let G := S.filter fun n ↦ (canonicalSquarePart (v n) : ℝ) ^ 2 ≤ L ∧ (largeOddKernel Y (v n) : ℝ) ≤ K
  let B := S.filter fun n ↦ L < (canonicalSquarePart (v n) : ℝ) ^ 2
  let C := S.filter fun n ↦ K < (largeOddKernel Y (v n) : ℝ)
  have hcover : S ⊆ (G ∪ B) ∪ C := by
    intro n hn
    by_cases hs : (canonicalSquarePart (v n) : ℝ) ^ 2 ≤ L
    · by_cases hk : (largeOddKernel Y (v n) : ℝ) ≤ K
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn, hs, hk⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hn, lt_of_not_ge hk⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn, lt_of_not_ge hs⟩))
  have hcount : S.card ≤ G.card + B.card + C.card :=
    (card_le_card hcover).trans ((card_union_le (s := G ∪ B) (t := C)).trans
      (Nat.add_le_add_right (card_union_le (s := G) (t := B)) _))
  change k ≤ G.card
  change B.card ≤ 1 at hsquare
  change C.card < t at hlarge
  omega

end PaperP1.KernelSquareBudget
