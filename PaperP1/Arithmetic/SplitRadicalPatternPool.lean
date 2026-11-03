module

public import PaperP1.Combinatorics.BoundedSubsets
public import PaperP1.Combinatorics.BoundedIntegerMotifs
public import PaperP1.Arithmetic.SmoothSupportBounds
public import Mathlib.Data.Fintype.Pi

/-! # Actual bounded offset and small-prime coefficient patterns for split radical systems -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalPatternPool

open Finset PaperP1.BoundedIntegerMotifs PaperP1.DefectCounting

abbrev Pattern (k : ℕ) := ((Fin k → Finset ℤ) × (Fin k → ℤ)) × (Fin k → Finset ℕ)

def leftPool (L K : ℕ) : Finset (Finset ℤ) := BoundedSubsets.sets (offsets (L + 1)) K

def leftPatterns (k L K : ℕ) : Finset (Fin k → Finset ℤ) := Fintype.piFinset fun _ ↦ leftPool L K

def rightPatterns (k L : ℕ) : Finset (Fin k → ℤ) := Fintype.piFinset fun _ ↦ offsets (L + 1)

def codePatterns (k H : ℕ) : Finset (Fin k → Finset ℕ) :=
  Fintype.piFinset fun _ ↦ (smallPrimesUpTo H).powerset

def pool (k L H K : ℕ) : Finset (Pattern k) := (leftPatterns k L K ×ˢ rightPatterns k L) ×ˢ codePatterns k H

def coefficient {k : ℕ} (p : Pattern k) (i : Fin k) : ℤ := ((p.2 i).prod id : ℕ)

theorem mem_pool (k L H K : ℕ) (p : Pattern k) : p ∈ pool k L H K ↔
    (∀ i, p.1.1 i ⊆ offsets (L + 1) ∧ (p.1.1 i).card ≤ K) ∧
    (∀ i, p.1.2 i ∈ offsets (L + 1)) ∧ (∀ i, p.2 i ⊆ smallPrimesUpTo H) := by
  simp only [pool, mem_product, leftPatterns, rightPatterns, codePatterns, Fintype.mem_piFinset,
    leftPool, BoundedSubsets.mem_sets, mem_powerset]
  exact and_assoc

theorem offset_card_bound (k L K : ℕ) :
    (leftPatterns k L K ×ˢ rightPatterns k L).card ≤
      ((K + 1) * 4 ^ K * 3) ^ k * (L + 1) ^ ((K + 1) * k) := by
  let W := L + 1
  have hW : 1 ≤ W := by omega
  have hfour : (offsets W).card + 1 ≤ 4 * W := by rw [offsets_card]; omega
  have hleft : (leftPool L K).card ≤ ((K + 1) * 4 ^ K) * W ^ K := by
    calc
      _ ≤ (K + 1) * ((offsets W).card + 1) ^ K := BoundedSubsets.card_sets _ K
      _ ≤ (K + 1) * (4 * W) ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hfour K)
      _ = _ := by rw [mul_pow]; ring
  have hright : (offsets W).card ≤ 3 * W := by rw [offsets_card]; omega
  have hcard : (leftPatterns k L K ×ˢ rightPatterns k L).card =
      (leftPool L K).card ^ k * (offsets W).card ^ k := by
    rw [card_product, leftPatterns, rightPatterns, Fintype.card_piFinset_const, Fintype.card_piFinset_const]
  rw [hcard]
  calc
    _ ≤ (((K + 1) * 4 ^ K) * W ^ K) ^ k * (3 * W) ^ k :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hleft k) (Nat.pow_le_pow_left hright k)
    _ = (((K + 1) * 4 ^ K * 3) * W ^ (K + 1)) ^ k := by
      rw [← mul_pow]
      congr 1
      rw [pow_succ]
      ring
    _ = _ := by rw [mul_pow, ← pow_mul]

theorem code_card (k H : ℕ) : (codePatterns k H).card = (smallPrimesUpTo H).powerset.card ^ k := by
  rw [codePatterns, Fintype.card_piFinset_const]

theorem coefficient_pos {k L H K : ℕ} {p : Pattern k} (hp : p ∈ pool k L H K) (i : Fin k) :
    0 < coefficient p i := by
  have h := SmoothSupportBounds.supportProduct_pos (((mem_pool k L H K p).mp hp).2.2 i)
  change (0 : ℤ) < ((p.2 i).prod id : ℕ)
  exact_mod_cast h

theorem coefficient_natAbs {k : ℕ} (p : Pattern k) (i : Fin k) :
    (coefficient p i).natAbs = (p.2 i).prod id := by simp only [coefficient, Int.natAbs_natCast]

theorem coefficient_le_four_pow {k L H K : ℕ} {p : Pattern k} (hp : p ∈ pool k L H K) (i : Fin k) :
    (coefficient p i).natAbs ≤ 4 ^ H := by
  rw [coefficient_natAbs]
  exact SmoothSupportBounds.supportProduct_le_four_pow (((mem_pool k L H K p).mp hp).2.2 i)

theorem left_bound {k L H K : ℕ} {p : Pattern k} (hp : p ∈ pool k L H K) (i : Fin k)
    (z : ℤ) (hz : z ∈ p.1.1 i) : z.natAbs ≤ L + 1 :=
  (subset_offsets (L + 1) (p.1.1 i)).mp (((mem_pool k L H K p).mp hp).1 i).1 z hz

theorem right_bound {k L H K : ℕ} {p : Pattern k} (hp : p ∈ pool k L H K) (i : Fin k) :
    (p.1.2 i).natAbs ≤ L + 1 := by
  have hmem := ((mem_pool k L H K p).mp hp).2.1 i
  have habs : |p.1.2 i| ≤ ((L + 1 : ℕ) : ℤ) := abs_le.mpr (mem_Icc.mp hmem)
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

end PaperP1.SplitRadicalPatternPool
