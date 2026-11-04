module

public import PaperP1.Arithmetic.OddPrimePivot
public import PaperP1.Arithmetic.RankinSmallKernel
public import PaperP1.Model.FiniteRademacher

/-! # Small actual pivots and the windows which contain them

These are the largest primes with odd valuation, including the prime two.
The counts are actual integer and start populations, with no smooth-value
short-interval hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolylogPivotExceptions

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.OddPrimePivot
  PaperP1.SmallKernelCount PaperP1.LargeOddKernel

local instance polylogPivotDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem pivot_subset_small_kernel (X Y : ℕ) (hY : 1 ≤ Y) :
    pivotValues X Y ⊆ smallKernelValues Y 1 X := by
  intro n hn
  obtain ⟨hn, hp⟩ := mem_filter.mp hn
  obtain ⟨hn1, hnX⟩ := mem_Icc.mp hn
  have hk := (largeOddKernel_eq_one_iff Y n).mpr ((largestOddPrime_le_iff hY).mp hp)
  exact mem_smallKernelValues.mpr ⟨hn1, hnX, hk.le⟩

theorem pivot_count_rankin (X Y : ℕ) (hY : 1 ≤ Y)
    (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) :
    ((pivotValues X Y).card : ℝ) ≤
      (X : ℝ) ^ σ * (1 / (1 - σ)) * Real.exp ((Y : ℝ) ^ (1 - σ) / (1 - σ)) := by
  have hc : ((pivotValues X Y).card : ℝ) ≤ (smallKernelValues Y 1 X).card := by
    exact_mod_cast card_le_card (pivot_subset_small_kernel X Y hY)
  have hb := card_smallKernelValues_le_power Y 1 X σ hσ hσ1
  simpa only [Nat.cast_one, Real.one_rpow] using hc.trans hb

def badAt (N B Y : ℕ) (i : Fin B) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ largestOddPrime (x - 1 + i.val) ≤ Y

def badWindows (N B Y : ℕ) : Finset ℕ :=
  univ.biUnion (badAt N B Y)

theorem mem_badWindows {N B Y x : ℕ} :
    x ∈ badWindows N B Y ↔ x ∈ dyadicBlock N ∧
      ∃ i : Fin B, largestOddPrime (x - 1 + i.val) ≤ Y := by
  simp only [badWindows, mem_biUnion, mem_univ, true_and, badAt, mem_filter]
  constructor
  · rintro ⟨i, hx, hi⟩
    exact ⟨hx, i, hi⟩
  · rintro ⟨hx, i, hi⟩
    exact ⟨i, hx, hi⟩

theorem badAt_card {N B Y : ℕ} (hN : 2 ≤ N) (hBN : B ≤ N) (i : Fin B) :
    (badAt N B Y i).card ≤ (pivotValues (3 * N) Y).card := by
  apply card_le_card_of_injOn (fun x ↦ x - 1 + i.val)
  · intro x hx
    dsimp only
    obtain ⟨hx, hi⟩ := mem_filter.mp hx
    obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
    have hiB := i.isLt
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hi⟩
  · intro x hx y hy hxy
    change x - 1 + i.val = y - 1 + i.val at hxy
    have hxlo := (mem_Ico.mp (mem_filter.mp hx).1).1
    have hylo := (mem_Ico.mp (mem_filter.mp hy).1).1
    omega

theorem badWindows_card {N B Y : ℕ} (hN : 2 ≤ N) (hBN : B ≤ N) :
    (badWindows N B Y).card ≤ B * (pivotValues (3 * N) Y).card := by
  calc
    _ ≤ ∑ i : Fin B, (badAt N B Y i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin B, (pivotValues (3 * N) Y).card :=
      sum_le_sum fun i _ ↦ badAt_card hN hBN i
    _ = _ := by simp

def retained (N B Y : ℕ) : Finset ℕ := (dyadicBlock N) \ badWindows N B Y

theorem mem_retained {N B Y x : ℕ} : x ∈ retained N B Y ↔
    x ∈ dyadicBlock N ∧ ∀ i : Fin B, Y < largestOddPrime (x - 1 + i.val) := by
  simp only [retained, mem_sdiff, mem_badWindows]
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨hx, fun i ↦ ?_⟩
    by_contra hi
    exact hn ⟨hx, i, by omega⟩
  · rintro ⟨hx, hi⟩
    exact ⟨hx, fun ⟨_, i, h⟩ ↦ (not_le_of_gt (hi i)) h⟩

theorem retained_deletion_ledger (N B Y : ℕ) :
    (retained N B Y).card + (badWindows N B Y).card = N := by
  have hs : badWindows N B Y ⊆ dyadicBlock N := fun _ hx ↦ (mem_badWindows.mp hx).1
  simpa only [retained, dyadicBlock_card] using card_sdiff_add_card_eq_card hs

end PaperP1.PolylogPivotExceptions
