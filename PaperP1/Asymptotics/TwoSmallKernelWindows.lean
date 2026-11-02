module

public import PaperP1.Asymptotics.TwoSmallKernelLower
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # The literal window count with two individually small odd kernels has the claimed lower exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelWindows

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedWindowSets PaperP1.LargeOddKernel

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def smallValues (H x L : ℕ) (T : ℝ) : Finset ℕ := (values x L).filter fun n ↦ (largeOddKernel H n : ℝ) ≤ T

def windows (N L H : ℕ) (T : ℝ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ 2 ≤ (smallValues H x L T).card

theorem two_neighbors {H x L : ℕ} {T : ℝ} (hx : 0 < x) (hL : 2 ≤ L)
    (hfirst : (largeOddKernel H x : ℝ) ≤ T) (hsecond : (largeOddKernel H (x + 1) : ℝ) ≤ T) :
    2 ≤ (smallValues H x L T).card := by
  have hxmem : x ∈ values x L := by rw [values_eq_interval hx]; exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hx1mem : x + 1 ∈ values x L := by rw [values_eq_interval hx]; exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hsub : ({x, x + 1} : Finset ℕ) ⊆ smallValues H x L T := by
    intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · exact mem_filter.mpr ⟨hxmem, hfirst⟩
    · rw [mem_singleton.mp hn]
      exact mem_filter.mpr ⟨hx1mem, hsecond⟩
  have hcard : ({x, x + 1} : Finset ℕ).card = 2 := by simp
  rw [← hcard]
  exact card_le_card hsub

theorem admissible_subset {N L H : ℕ} {T : ℝ} (hN : 0 < N) (hL : 2 ≤ L) :
    TwoAdjacentSmallKernels.admissible N H T ⊆ windows N L H T := by
  intro x hx
  obtain ⟨hinterval, hfirst, hsecond⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hinterval, two_neighbors (hN.trans_le (mem_Ico.mp hinterval).1) hL hfirst hsecond⟩

theorem uniform_lower (β ε : ℝ) (hβlo : 1 / 2 < β) (hβhi : β < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ, 2 ≤ L →
      (N : ℝ) ^ (β - ε) ≤ ((windows N L H ((N : ℝ) ^ β)).card : ℝ) := by
  obtain ⟨N₀, hN₀, hu⟩ := TwoSmallKernelLower.uniform_lower β ε hβlo hβhi hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hL
  exact (hu N hN H).trans (by exact_mod_cast card_le_card (admissible_subset (by omega : 0 < N) hL))

theorem critical_lower (β ε C : ℝ) (hβlo : 1 / 2 < β) (hβhi : β < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ (β - ε) ≤ ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) := by
  obtain ⟨NK, _hNK, hk⟩ := uniform_lower β ε hβlo hβhi hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 3
  refine ⟨max 10 (max NK NG), by omega, ?_⟩
  intro N hN L hband
  have hL : 2 ≤ L := by have hh := (hg N (by omega) L hband).2.1; omega
  exact hk N (by omega) L (L + 1) hL

end PaperP1.TwoSmallKernelWindows
