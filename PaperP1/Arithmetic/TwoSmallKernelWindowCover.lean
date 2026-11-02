module

public import PaperP1.Asymptotics.TwoSmallKernelWindows

/-! # A literal finite offset cover of windows with two individually small kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelWindowCover

open Finset PaperP1.TwoSmallKernelWindows PaperP1.NormalizedWindowSets
  PaperP1.LargeOddKernel PaperP1.Arithmetic PaperP1.Model

theorem ordered_values {N L H x : ℕ} {T : ℝ} (hx : x ∈ windows N L H T) :
    ∃ n ∈ smallValues H x L T, ∃ m ∈ smallValues H x L T, n < m := by
  have hh := (mem_filter.mp hx).2
  obtain ⟨n, hn, m, hm, hnm⟩ := one_lt_card.mp (show 1 < (smallValues H x L T).card by omega)
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact ⟨n, hn, m, hm, hlt⟩
  · exact ⟨m, hm, n, hn, hlt⟩

theorem witness {N L H x : ℕ} {T : ℝ} (hN : 0 < N) (hx : x ∈ windows N L H T) :
    ∃ i ∈ range (L + 1), ∃ h ∈ Icc 1 L,
      (largeOddKernel H (x - 1 + i) : ℝ) ≤ T ∧ (largeOddKernel H (x - 1 + i + h) : ℝ) ≤ T := by
  have hxpos : 0 < x := hN.trans_le (mem_Ico.mp (mem_filter.mp hx).1).1
  obtain ⟨n, hn, m, hm, hlt⟩ := ordered_values hx
  obtain ⟨hnV, hnK⟩ := mem_filter.mp hn
  obtain ⟨hmV, hmK⟩ := mem_filter.mp hm
  rw [values_eq_interval hxpos] at hnV hmV
  obtain ⟨hnlo, hnhi⟩ := mem_Ico.mp hnV
  obtain ⟨hmlo, hmhi⟩ := mem_Ico.mp hmV
  refine ⟨n - (x - 1), mem_range.mpr (by omega), m - n, mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
  · simpa only [Nat.add_sub_of_le hnlo] using hnK
  · have heq : x - 1 + (n - (x - 1)) + (m - n) = m := by omega
    simpa only [heq] using hmK

theorem translated_injective {N : ℕ} (hN : 2 ≤ N) (i : ℕ) (S : Finset ℕ)
    (hS : S ⊆ dyadicBlock N) : Set.InjOn (fun x : ℕ ↦ x - 1 + i) (↑S : Set ℕ) := by
  intro x hx y hy heq
  have hxlo := (mem_Ico.mp (hS hx)).1
  have hylo := (mem_Ico.mp (hS hy)).1
  change x - 1 + i = y - 1 + i at heq
  omega

theorem translated_heights {N L x i h : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hx : x ∈ dyadicBlock N) (hi : i ∈ range (L + 1)) (hh : h ∈ Icc 1 L) :
    0 < x - 1 + i ∧ N ≤ 2 * (x - 1 + i) ∧ x - 1 + i ≤ 3 * N ∧ x - 1 + i + h ≤ 4 * N := by
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  have hi' := mem_range.mp hi
  have hh' := mem_Icc.mp hh
  omega

end PaperP1.TwoSmallKernelWindowCover
