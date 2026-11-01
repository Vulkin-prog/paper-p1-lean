module

public import PaperP1.Arithmetic.RankinSmallKernel

/-! # Small-kernel values in arbitrary translated finite integer blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelBlocks

open Finset PaperP1.LargeOddKernel PaperP1.RankinSmallKernel

def offsetStarts (G : Finset ℤ) (H : ℕ) (T : ℝ) (u : ℤ) : Finset ℤ :=
  G.filter fun x ↦ 0 < x + u ∧ (largeOddKernel H (x + u).toNat : ℝ) ≤ T

def starts (G O : Finset ℤ) (H : ℕ) (T : ℝ) : Finset ℤ :=
  O.biUnion (offsetStarts G H T)

def selectedStarts (G : Finset ℤ) (V : ℤ → Finset ℕ) (H : ℕ) (T : ℝ) : Finset ℤ :=
  G.filter fun x ↦ ∃ n ∈ V x, (largeOddKernel H n : ℝ) ≤ T

theorem mem_starts {G O : Finset ℤ} {H : ℕ} {T : ℝ} {x : ℤ} :
    x ∈ starts G O H T ↔ x ∈ G ∧ ∃ u ∈ O, 0 < x + u ∧ (largeOddKernel H (x + u).toNat : ℝ) ≤ T := by
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := mem_biUnion.mp hx
    obtain ⟨hxG, hpos, hT⟩ := mem_filter.mp hxu
    exact ⟨hxG, u, hu, hpos, hT⟩
  · rintro ⟨hxG, u, hu, hpos, hT⟩
    exact mem_biUnion.mpr ⟨u, hu, mem_filter.mpr ⟨hxG, hpos, hT⟩⟩

theorem selected_subset {G O : Finset ℤ} {V : ℤ → Finset ℕ} {H : ℕ} {T : ℝ}
    (hV : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ (n : ℤ) - x ∈ O) :
    selectedStarts G V H T ⊆ starts G O H T := by
  intro x hx
  obtain ⟨hxG, n, hn, hT⟩ := mem_filter.mp hx
  obtain ⟨hnpos, hnoffset⟩ := hV x hxG n hn
  apply mem_starts.mpr
  refine ⟨hxG, (n : ℤ) - x, hnoffset, ?_, ?_⟩
  · have h : (0 : ℤ) < n := by exact_mod_cast hnpos
    omega
  · have heq : x + ((n : ℤ) - x) = n := by omega
    simpa only [heq, Int.toNat_natCast] using hT

theorem fixed_offset_card {G : Finset ℤ} {H X : ℕ} {T : ℝ} (u : ℤ)
    (hheight : ∀ x ∈ G, x + u ≤ (X : ℤ)) :
    (offsetStarts G H T u).card ≤ (values (X : ℝ) H T).card := by
  apply card_le_card_of_injOn (fun x : ℤ ↦ (x + u).toNat)
  · intro x hx
    obtain ⟨hxG, hxpos, hT⟩ := mem_filter.mp hx
    have hcast : ((x + u).toNat : ℤ) = x + u := Int.toNat_of_nonneg hxpos.le
    have hn : 1 ≤ (x + u).toNat := by omega
    have hnX : (x + u).toNat ≤ X := by have := hheight x hxG; omega
    have heq : truncatedKernel (H : ℝ) (x + u).toNat = largeOddKernel H (x + u).toNat := by
      simpa only [Nat.floor_natCast] using truncatedKernel_eq_floor (H : ℝ) (Nat.cast_nonneg H) (x + u).toNat
    refine (mem_values _ _ _ (Nat.cast_nonneg X) _).mpr ⟨hn, ?_, ?_⟩
    · exact_mod_cast hnX
    · rw [heq]
      exact hT
  · intro x hx y hy heq
    have hxpos := (mem_filter.mp hx).2.1
    have hypos := (mem_filter.mp hy).2.1
    change (x + u).toNat = (y + u).toNat at heq
    have hxc := Int.toNat_of_nonneg hxpos.le
    have hyc := Int.toNat_of_nonneg hypos.le
    omega

theorem starts_card {G O : Finset ℤ} {H X : ℕ} (T : ℝ)
    (hheight : ∀ x ∈ G, ∀ u ∈ O, x + u ≤ (X : ℤ)) :
    (starts G O H T).card ≤ O.card * (values (X : ℝ) H T).card := by
  calc
    _ ≤ ∑ u ∈ O, (offsetStarts G H T u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ O, (values (X : ℝ) H T).card :=
      sum_le_sum (fun u hu ↦ fixed_offset_card u (fun x hx ↦ hheight x hx u hu))
    _ = _ := by simp

theorem finite_exp_bound {G O : Finset ℤ} {H X : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (hheight : ∀ x ∈ G, ∀ u ∈ O, x + u ≤ (X : ℤ)) :
    ((starts G O H T).card : ℝ) ≤
      2 * O.card * Real.sqrt X * Real.sqrt T * Real.exp (2 * Real.sqrt H) := by
  have hcard : ((starts G O H T).card : ℝ) ≤ (O.card : ℝ) * (values (X : ℝ) H T).card := by
    exact_mod_cast starts_card T hheight
  refine hcard.trans ?_
  have h := mul_le_mul_of_nonneg_left
    (rankin_half X H T (Nat.cast_nonneg X) (Nat.cast_nonneg H) hT) (Nat.cast_nonneg O.card)
  convert h using 1; ring

end PaperP1.SmallKernelBlocks
