module

public import PaperP1.Asymptotics.CanonicalInteriorSmoothCount
public import PaperP1.Asymptotics.TwoSmallKernelElementaryUpper

/-! # The sharp two-small-kernel upper count for the entire actual comparable population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpTwoSmallKernelCount

open Finset PaperP1.TwoSmallKernelSquareParts PaperP1.SmallPrimeBudget
open PaperP1.LargeOddKernel PaperP1.DefectivePredicate

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (D K A ε : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H h : ℕ, ∀ T : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A → 0 ≤ T →
      ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ N ≤ 2 * n ∧ n ≤ 3 * N ∧ n + h ≤ 4 * N ∧
        (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T) →
      (S.card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  classical
  obtain ⟨NS, _hNS, hs⟩ := TwoSmallKernelSmallSquares.uniform_count D (ε / 2) hD (by positivity)
  obtain ⟨NV, hv⟩ := TwoSmallKernelCount.comparable_count 4 (by norm_num) D K A (ε / 2) hD (by positivity)
  obtain ⟨NW, hw⟩ := CanonicalInteriorSmoothCount.uniform_count hHB hNG (1 / 4) D K A (ε / 2)
    (by norm_num) (by norm_num) hD hK hA (by positivity)
  obtain ⟨Nh, hNh⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (48 * K) A (ε / 2) (by positivity)
  obtain ⟨Nc, hNc⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow 20 0 (ε / 2) (by positivity)
  refine ⟨max 4 (max NS (max NV (max NW (max Nh Nc)))), by omega, ?_⟩
  intro N hN H h T hH hh hshift hT S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let R := (N : ℝ) ^ (7 / 12 : ℝ)
  let B := T + R
  let U := S.filter (fun n ↦ ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ≤ 4 * Real.sqrt N)
  let V := S.filter (fun n ↦ ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ))
  let W := S.filter (fun n ↦ 4 * Real.sqrt N < ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ∧
    4 * (N : ℝ) ^ (1 / 4 : ℝ) < ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ))
  have hU : (U.card : ℝ) ≤ (24 * h * T + 4 * Real.sqrt N) * (N : ℝ) ^ (ε / 2) := by
    apply hs N (by omega) H h T (4 * Real.sqrt N) hH hh hT (by positivity) U
    intro n hnU
    obtain ⟨hnS, hprod⟩ := mem_filter.mp hnU
    obtain ⟨hnpos, hnlo, hnhi, hmhi, hk₁, hk₂⟩ := hS n hnS
    exact ⟨hnpos, hnlo, hnhi, hmhi, hk₁, hk₂, hprod⟩
  have hV : (V.card : ℝ) ≤ (4 * (N : ℝ) ^ (1 / 4 : ℝ)) * (N : ℝ) ^ (ε / 2) := by
    apply hv N (by omega) H h (4 * (N : ℝ) ^ (1 / 4 : ℝ)) hH hh hshift (by positivity) V
    intro n hnV
    obtain ⟨hnS, hprod⟩ := mem_filter.mp hnV
    obtain ⟨_hnpos, hnlo, hnhi, _hmhi, _hk₁, _hk₂⟩ := hS n hnS
    refine ⟨by omega, by omega, 0, (h : ℤ), by simp, by simp, by exact_mod_cast (Ne.symm hh.ne'), ?_⟩
    simpa only [TwoSmallKernelFibres.largeKernel, LinearKernelFibres.value, add_zero,
      ← Nat.cast_add, Int.natAbs_natCast, Nat.cast_mul] using hprod
  have hW : (W.card : ℝ) ≤ B * (N : ℝ) ^ (ε / 2) := by
    apply hw N (by omega) H h T hH hh hshift hT W
    · intro n hnW
      obtain ⟨hnpos, hnlo, hnhi, hmhi, _hk₁, _hk₂⟩ := hS n (mem_filter.mp hnW).1
      exact ⟨hnpos, hnlo, hnhi, hmhi⟩
    · intro n hnW
      obtain ⟨_hnpos, _hnlo, _hnhi, _hmhi, hk₁, hk₂⟩ := hS n (mem_filter.mp hnW).1
      exact ⟨hk₁, hk₂⟩
    · exact fun n hnW ↦ (mem_filter.mp hnW).2
  have hcover : S ⊆ U ∪ V ∪ W := by
    intro n hnS
    by_cases hd : ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ≤ 4 * Real.sqrt N
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnS, hd⟩))
    · by_cases hu : ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnS, hu⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hnS, lt_of_not_ge hd, lt_of_not_ge hu⟩)
  have hcard : (S.card : ℝ) ≤ (U.card : ℝ) + V.card + W.card := by
    have hu := (card_union_le (U ∪ V) W).trans (Nat.add_le_add_right (card_union_le U V) W.card)
    exact_mod_cast (card_le_card hcover).trans hu
  have hR : 0 ≤ R := Real.rpow_nonneg hn.le _
  have hB : 0 ≤ B := add_nonneg hT hR
  have hp : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hn.le _
  have hroot : Real.sqrt N ≤ R := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1 / 2 : ℝ) ≤ 7 / 12)
  have hquarter : (N : ℝ) ^ (1 / 4 : ℝ) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1 / 4 : ℝ) ≤ 7 / 12)
  have h48 : 48 * (h : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hm : 48 * (h : ℝ) ≤ (48 * K) * (Real.log N) ^ A := by linarith only [hshift]
    exact hm.trans (hNh N (by omega))
  have h20 : (20 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by simpa only [Real.rpow_zero, mul_one] using hNc N (by omega)
  have hpref : 24 * (h : ℝ) + 10 ≤ (N : ℝ) ^ (ε / 2) := by linarith only [h48, h20]
  have htotal : (S.card : ℝ) ≤ (24 * h * T + 4 * Real.sqrt N + 4 * (N : ℝ) ^ (1 / 4 : ℝ) + B) * (N : ℝ) ^ (ε / 2) := by
    nlinarith only [hcard, hU, hV, hW]
  have hcoeff : 24 * (h : ℝ) * T + 4 * Real.sqrt N + 4 * (N : ℝ) ^ (1 / 4 : ℝ) + B ≤ (24 * (h : ℝ) + 10) * B := by
    have hr := mul_nonneg (show 0 ≤ 24 * (h : ℝ) + 1 by positivity) hR
    have ht := mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hT
    dsimp only [B]
    nlinarith only [hroot, hquarter, hr, ht]
  calc
    _ ≤ (24 * h * T + 4 * Real.sqrt N + 4 * (N : ℝ) ^ (1 / 4 : ℝ) + B) * (N : ℝ) ^ (ε / 2) := htotal
    _ ≤ ((24 * (h : ℝ) + 10) * B) * (N : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_right hcoeff hp
    _ ≤ ((N : ℝ) ^ (ε / 2) * B) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref hB) hp
    _ = _ := by
      calc
        _ = B * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

end PaperP1.SharpTwoSmallKernelCount
