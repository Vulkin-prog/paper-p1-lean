module

public import PaperP1.Arithmetic.SmallKernelBlocks
public import Mathlib.Data.Int.Interval

/-! # Exact ordered-offset cover for two small kernels in arbitrary selected blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelBlocks

open Finset PaperP1.LargeOddKernel

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def offsetPairStarts (G : Finset ℤ) (H : ℕ) (T : ℝ) (u v : ℤ) : Finset ℤ :=
  G.filter (fun x ↦ 0 < x + u ∧ 0 < x + v ∧
    (largeOddKernel H (x + u).toNat : ℝ) ≤ T ∧ (largeOddKernel H (x + v).toNat : ℝ) ≤ T)

def starts (G O : Finset ℤ) (H : ℕ) (T : ℝ) : Finset ℤ :=
  ((O ×ˢ O).filter (fun uv ↦ uv.1 < uv.2)).biUnion (fun uv ↦ offsetPairStarts G H T uv.1 uv.2)

def selectedStarts (G : Finset ℤ) (V : ℤ → Finset ℕ) (H : ℕ) (T : ℝ) : Finset ℤ :=
  G.filter (fun x ↦ 2 ≤ ((V x).filter (fun n ↦ (largeOddKernel H n : ℝ) ≤ T)).card)

theorem ordered_witness {G : Finset ℤ} {V : ℤ → Finset ℕ} {H : ℕ} {T : ℝ} {x : ℤ}
    (hx : x ∈ selectedStarts G V H T) :
    ∃ n ∈ V x, ∃ m ∈ V x, n < m ∧ (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H m : ℝ) ≤ T := by
  have hh := (mem_filter.mp hx).2
  obtain ⟨n, hn, m, hm, hnm⟩ := one_lt_card.mp (show 1 < ((V x).filter (fun n ↦ (largeOddKernel H n : ℝ) ≤ T)).card by omega)
  obtain ⟨hnV, hnK⟩ := mem_filter.mp hn
  obtain ⟨hmV, hmK⟩ := mem_filter.mp hm
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact ⟨n, hnV, m, hmV, hlt, hnK, hmK⟩
  · exact ⟨m, hmV, n, hnV, hlt, hmK, hnK⟩

theorem selected_subset {G O : Finset ℤ} {V : ℤ → Finset ℕ} {H : ℕ} {T : ℝ}
    (hV : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ (n : ℤ) - x ∈ O) :
    selectedStarts G V H T ⊆ starts G O H T := by
  intro x hx
  have hxG := (mem_filter.mp hx).1
  obtain ⟨n, hn, m, hm, hnm, hnK, hmK⟩ := ordered_witness hx
  obtain ⟨hnpos, hnO⟩ := hV x hxG n hn
  obtain ⟨hmpos, hmO⟩ := hV x hxG m hm
  have horder : (n : ℤ) - x < (m : ℤ) - x := by
    have hnmZ : (n : ℤ) < m := by exact_mod_cast hnm
    omega
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hmpos
  apply mem_biUnion.mpr
  refine ⟨((n : ℤ) - x, (m : ℤ) - x), mem_filter.mpr ⟨mem_product.mpr ⟨hnO, hmO⟩, horder⟩, ?_⟩
  apply mem_filter.mpr
  refine ⟨hxG, by omega, by omega, ?_, ?_⟩
  · have heq : x + ((n : ℤ) - x) = n := by omega
    simpa only [heq, Int.toNat_natCast] using hnK
  · have heq : x + ((m : ℤ) - x) = m := by omega
    simpa only [heq, Int.toNat_natCast] using hmK

theorem pair_translation (x u v : ℤ) (hu : 0 < x + u) (huv : u < v) :
    (x + u).toNat + (v - u).toNat = (x + v).toNat := by
  have hv : 0 ≤ x + v := by omega
  have hg : 0 ≤ v - u := by omega
  have hn := Int.toNat_of_nonneg hu.le
  have hm := Int.toNat_of_nonneg hv
  have hh := Int.toNat_of_nonneg hg
  omega

theorem fixed_pair_injective (G : Finset ℤ) (H : ℕ) (T : ℝ) (u v : ℤ) :
    Set.InjOn (fun x : ℤ ↦ (x + u).toNat) (↑(offsetPairStarts G H T u v) : Set ℤ) := by
  intro x hx y hy heq
  have hxpos := (mem_filter.mp hx).2.1
  have hypos := (mem_filter.mp hy).2.1
  change (x + u).toNat = (y + u).toNat at heq
  have hxc := Int.toNat_of_nonneg hxpos.le
  have hyc := Int.toNat_of_nonneg hypos.le
  omega

theorem offset_gap (R : ℕ) (u v : ℤ) (hu : u ∈ Icc (-(R : ℤ)) R)
    (hv : v ∈ Icc (-(R : ℤ)) R) (huv : u < v) :
    0 < (v - u).toNat ∧ (v - u).toNat ≤ 2 * R := by
  have hu' := mem_Icc.mp hu
  have hv' := mem_Icc.mp hv
  have hg : 0 ≤ v - u := by omega
  have hc := Int.toNat_of_nonneg hg
  omega

end PaperP1.TwoSmallKernelBlocks
