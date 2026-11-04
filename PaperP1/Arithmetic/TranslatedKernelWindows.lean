module

public import PaperP1.Arithmetic.SmallKernelWindows

/-! # One and two small kernels on an arbitrary translated interval of starts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TranslatedKernelWindows

open Finset PaperP1.LargeOddKernel PaperP1.RankinSmallKernel

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def oneStarts (N H U : ℕ) (T : ℝ) : Finset ℕ :=
  (Ico U (U + N)).filter fun x ↦ ∃ i : Fin H, (largeOddKernel H (x - 1 + i.val) : ℝ) ≤ T

def twoStarts (N H U : ℕ) (T : ℝ) : Finset ℕ :=
  (Ico U (U + N)).filter fun x ↦ ∃ i j : Fin H, i ≠ j ∧
    (largeOddKernel H (x - 1 + i.val) : ℝ) ≤ T ∧ (largeOddKernel H (x - 1 + j.val) : ℝ) ≤ T

theorem one_cover {N H U : ℕ} (T : ℝ) (hH : H ≤ N) (hU : 2 ≤ U) (hUN : U ≤ N) :
    oneStarts N H U T ⊆ (values (3 * N) H T).biUnion (SmallKernelWindows.placements H) := by
  intro x hx
  obtain ⟨hx, i, hT⟩ := mem_filter.mp hx
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  let n := x - 1 + i.val
  have hi := i.isLt
  have heq : truncatedKernel (H : ℝ) n = largeOddKernel H n := by
    simpa only [Nat.floor_natCast] using truncatedKernel_eq_floor (H : ℝ) (Nat.cast_nonneg H) n
  have hn : n ∈ values (3 * N) H T := by
    apply (mem_values _ _ _ (by positivity) n).mpr
    refine ⟨by dsimp [n]; omega, ?_, ?_⟩
    · exact_mod_cast (show n ≤ 3 * N by dsimp [n]; omega)
    · rw [heq]
      exact hT
  refine mem_biUnion.mpr ⟨n, hn, mem_image.mpr ⟨i, mem_univ _, ?_⟩⟩
  dsimp [n]
  omega

theorem one_card {N H U : ℕ} (T : ℝ) (hH : H ≤ N) (hU : 2 ≤ U) (hUN : U ≤ N) :
    (oneStarts N H U T).card ≤ H * (values (3 * N) H T).card := by
  calc
    _ ≤ ((values (3 * N) H T).biUnion (SmallKernelWindows.placements H)).card :=
      card_le_card (one_cover T hH hU hUN)
    _ ≤ ∑ n ∈ values (3 * N) H T, (SmallKernelWindows.placements H n).card := card_biUnion_le
    _ ≤ ∑ _n ∈ values (3 * N) H T, H := by
      apply sum_le_sum
      intro n _
      exact card_image_le.trans_eq (by simp)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; ring

theorem one_finite_exp_bound {N H U : ℕ} (T : ℝ) (hH : H ≤ N) (hU : 2 ≤ U) (hUN : U ≤ N) (hT : 0 ≤ T) :
    ((oneStarts N H U T).card : ℝ) ≤
      2 * H * Real.sqrt (3 * N) * Real.sqrt T * Real.exp (2 * Real.sqrt H) := by
  have hcast : ((oneStarts N H U T).card : ℝ) ≤
      (H : ℝ) * ((values (3 * N) H T).card : ℝ) := by exact_mod_cast one_card T hH hU hUN
  refine hcast.trans ?_
  have hh := mul_le_mul_of_nonneg_left
    (rankin_half (3 * N) H T (by positivity) (Nat.cast_nonneg H) hT) (Nat.cast_nonneg H)
  convert hh using 1
  ring

theorem two_witness {N H U x : ℕ} {T : ℝ} (hx : x ∈ twoStarts N H U T) :
    ∃ i ∈ range H, ∃ h ∈ Icc 1 H,
      (largeOddKernel H (x - 1 + i) : ℝ) ≤ T ∧ (largeOddKernel H (x - 1 + i + h) : ℝ) ≤ T := by
  obtain ⟨_hx, i, j, hij, hki, hkj⟩ := mem_filter.mp hx
  have hne : i.val ≠ j.val := fun he ↦ hij (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨i.val, mem_range.mpr i.isLt, j.val - i.val, mem_Icc.mpr ⟨by omega, by have hh := j.isLt; omega⟩,
      hki, ?_⟩
    simpa only [show x - 1 + i.val + (j.val - i.val) = x - 1 + j.val by omega] using hkj
  · refine ⟨j.val, mem_range.mpr j.isLt, i.val - j.val, mem_Icc.mpr ⟨by omega, by have hh := i.isLt; omega⟩,
      hkj, ?_⟩
    simpa only [show x - 1 + j.val + (i.val - j.val) = x - 1 + i.val by omega] using hki

theorem translated_injective {N U : ℕ} (hU : 2 ≤ U) (i : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Ico U (U + N)) : Set.InjOn (fun x : ℕ ↦ x - 1 + i) (↑S : Set ℕ) := by
  intro x hx y hy heq
  have hxlo := (mem_Ico.mp (hS hx)).1
  have hylo := (mem_Ico.mp (hS hy)).1
  change x - 1 + i = y - 1 + i at heq
  omega

theorem translated_heights {N H U x i h : ℕ} (hU : 2 ≤ U) (hUN : U ≤ N) (hUhalf : N + 2 ≤ 2 * U)
    (hH : H ≤ N) (hx : x ∈ Ico U (U + N)) (hi : i ∈ range H) (hh : h ∈ Icc 1 H) :
    0 < x - 1 + i ∧ N ≤ 2 * (x - 1 + i) ∧ x - 1 + i ≤ 3 * N ∧ x - 1 + i + h ≤ 4 * N := by
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  have hi' := mem_range.mp hi
  have hh' := mem_Icc.mp hh
  omega

end PaperP1.TranslatedKernelWindows
