module

public import PaperP1.Asymptotics.SmallKernelBlockCount
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import Mathlib.Data.Int.Interval

/-! # The literal fixed-width one-small-kernel count for arbitrary selected subsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedWidthSmallKernel

open Finset PaperP1 PaperP1.SmallKernelBlocks PaperP1.CriticalBandScale

def offsets (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) R

def realSelectedStarts (G : Finset ℤ) (V : ℤ → Finset ℕ) (Y T : ℝ) : Finset ℤ :=
  G.filter fun x ↦ ∃ n ∈ V x, (PaperP1.RankinSmallKernel.truncatedKernel Y n : ℝ) ≤ T

theorem realSelectedStarts_eq (G : Finset ℤ) (V : ℤ → Finset ℕ) (Y T : ℝ) (hY : 0 ≤ Y) :
    realSelectedStarts G V Y T = selectedStarts G V ⌊Y⌋₊ T := by
  ext x
  simp only [realSelectedStarts, selectedStarts, mem_filter,
    PaperP1.RankinSmallKernel.truncatedKernel_eq_floor Y hY]

theorem offsets_card (R : ℕ) : (offsets R).card = 2 * R + 1 := by
  rw [offsets, Int.card_Icc]
  omega

/-- The first assertion of T1.13. Its separate two-small-kernel assertion remains open. -/
theorem one_kernel (K D : ℕ) (E C ε : ℝ) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, x ≤ (K * N : ℕ)) → ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ |(n : ℤ) - x| ≤ (D * (L + 1) : ℕ)) →
          ∀ T : ℝ, 0 ≤ T →
            ((selectedStarts G V H T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T := by
  let Q : ℝ := (2 * D + 1 : ℕ)
  obtain ⟨Nbase, hbase⟩ := SmallKernelBlockCount.arbitrary_selected_blocks
    (K + D : ℕ) (Q * upperScale) (E * upperScale) ε (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) upperScale_pos.le) (mul_nonneg hE upperScale_pos.le) hε
  obtain ⟨Nlog, hlog⟩ := critical_band_scale C
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) 1
  refine ⟨max Nbase (max Nlog Npoly), ?_⟩
  intro N hN L H hcrit hH G hG V hV T hT
  have hB : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N := (hlog N (by omega) L hcrit).2
  have hBN : L + 1 ≤ N := by
    have h := hpoly N (by omega) L hcrit
    simp only [pow_one, one_mul] at h
    exact_mod_cast h.le
  let O := offsets (D * (L + 1))
  have hO : (O.card : ℝ) ≤ (Q * upperScale) * Real.log N := by
    have hcard : O.card ≤ (2 * D + 1) * (L + 1) := by
      rw [offsets_card]
      nlinarith
    have hcast : (O.card : ℝ) ≤ Q * ((L + 1 : ℕ) : ℝ) := by
      dsimp [Q]
      exact_mod_cast hcard
    exact hcast.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg (2 * D + 1)))
  have hHlog : (H : ℝ) ≤ (E * upperScale) * Real.log N := by
    have hH' : (H : ℝ) ≤ E * ((L + 1 : ℕ) : ℝ) := by simpa only [Nat.cast_add, Nat.cast_one] using hH
    exact hH'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB hE)
  have hheight : ∀ x ∈ G, ∀ u ∈ O, x + u ≤ (((K + D) * N : ℕ) : ℤ) := by
    intro x hx u hu
    have hxhi := hG x hx
    have huhi : u ≤ ((D * (L + 1) : ℕ) : ℤ) := (mem_Icc.mp hu).2
    have hDN : ((D * (L + 1) : ℕ) : ℤ) ≤ ((D * N : ℕ) : ℤ) := by exact_mod_cast Nat.mul_le_mul_left D hBN
    have heq : ((K * N : ℕ) : ℤ) + ((D * N : ℕ) : ℤ) = (((K + D) * N : ℕ) : ℤ) := by push_cast; ring
    omega
  have hV' : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ (n : ℤ) - x ∈ O := by
    intro x hx n hn
    obtain ⟨hpos, habs⟩ := hV x hx n hn
    exact ⟨hpos, mem_Icc.mpr (abs_le.mp habs)⟩
  exact hbase N (by omega) G O H ((K + D) * N) hO hHlog (by push_cast; exact le_rfl)
    hheight V hV' T hT

theorem one_kernel_real (K D E C ε : ℝ) (_hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ E * (L + 1) →
      ∀ G : Finset ℤ, (∀ x ∈ G, (x : ℝ) ≤ K * N) → ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * (L + 1)) →
          ∀ T : ℝ, 0 ≤ T →
            ((selectedStarts G V H T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T := by
  obtain ⟨N₀, hN₀⟩ := one_kernel ⌈K⌉₊ ⌈D⌉₊ E C ε hE hε
  refine ⟨N₀, ?_⟩
  intro N hN L H hcrit hH G hG V hV T hT
  have hG' : ∀ x ∈ G, x ≤ (⌈K⌉₊ * N : ℕ) := by
    intro x hx
    have h : (x : ℝ) ≤ ((⌈K⌉₊ * N : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact (hG x hx).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (Nat.cast_nonneg N))
    exact_mod_cast h
  have hV' : ∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ |(n : ℤ) - x| ≤ (⌈D⌉₊ * (L + 1) : ℕ) := by
    intro x hx n hn
    obtain ⟨hpos, habs⟩ := hV x hx n hn
    refine ⟨hpos, ?_⟩
    have h : ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ ((⌈D⌉₊ * (L + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      exact habs.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (by positivity))
    exact_mod_cast h
  exact hN₀ N hN L H hcrit hH G hG' V hV' T hT

theorem one_kernel_real_cutoff (K D E C ε : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, 0 ≤ Y → Y ≤ E * (L + 1) →
        ∀ G : Finset ℤ, (∀ x ∈ G, (x : ℝ) ≤ K * N) → ∀ V : ℤ → Finset ℕ,
          (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ ((|(n : ℤ) - x| : ℤ) : ℝ) ≤ D * (L + 1)) →
            ∀ T : ℝ, 0 ≤ T →
              ((realSelectedStarts G V Y T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T := by
  obtain ⟨N₀, hN₀⟩ := one_kernel_real K D E C ε hD hE hε
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit Y hY hYband G hG V hV T hT
  rw [realSelectedStarts_eq G V Y T hY]
  exact hN₀ N hN L ⌊Y⌋₊ hcrit ((Nat.floor_le hY).trans hYband) G hG V hV T hT

end PaperP1.FixedWidthSmallKernel
