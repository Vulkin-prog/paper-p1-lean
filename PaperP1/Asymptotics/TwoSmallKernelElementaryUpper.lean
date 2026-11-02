module

public import PaperP1.Asymptotics.TwoSmallKernelSmallSquares
public import PaperP1.Asymptotics.TwoSmallKernelCount
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # An unconditional elementary upper count for two individually small odd kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelElementaryUpper

open Finset PaperP1.TwoSmallKernelSquareParts PaperP1.LargeOddKernel PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def squareCut (N : ℕ) : ℕ := Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ))

theorem squareCut_data {N : ℕ} (hN : 1 ≤ N) :
    0 < squareCut N ∧ (N : ℝ) ^ (2 / 3 : ℝ) ≤ squareCut N ∧
      (squareCut N : ℝ) ≤ 2 * (N : ℝ) ^ (2 / 3 : ℝ) ∧
      (4 * (N : ℝ)) ^ 2 ≤ (16 * (N : ℝ) ^ (2 / 3 : ℝ)) * (squareCut N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 1 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hn₁ (by norm_num)
  have hlo : (N : ℝ) ^ (2 / 3 : ℝ) ≤ squareCut N := Nat.le_ceil _
  have hpos : 0 < squareCut N := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn _)
  have hhi : (squareCut N : ℝ) ≤ 2 * (N : ℝ) ^ (2 / 3 : ℝ) := by
    have hh := (Nat.ceil_lt_add_one (Real.rpow_nonneg hn.le (2 / 3 : ℝ))).le
    change (squareCut N : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) + 1 at hh
    linarith only [hh, hr]
  have hcube : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    norm_num
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hn.le (2 / 3 : ℝ)) hlo 2
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 16 * (N : ℝ) ^ (2 / 3 : ℝ) by positivity)
  refine ⟨hpos, hlo, hhi, ?_⟩
  nlinarith only [hmul, hcube]

theorem uniform_count (D E A ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H h : ℕ, ∀ T : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < h → (h : ℝ) ≤ E * (Real.log N) ^ A → 0 ≤ T →
      ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ N ≤ 2 * n ∧ n ≤ 3 * N ∧ n + h ≤ 4 * N ∧
        (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T) →
      (S.card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NS, _hNS, hs⟩ := TwoSmallKernelSmallSquares.uniform_count D η hD hη
  obtain ⟨NL, hl⟩ := TwoSmallKernelCount.comparable_count 4 (by norm_num) D E A η hD hη
  obtain ⟨NH, hh⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (48 * E) A η hη
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption 36 0 η hη
  refine ⟨max 4 (max NS (max NL (max NH NC))), by omega, ?_⟩
  intro N hN H h T hH hhpos hhwidth hT S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hPpos, _hPlo, hPhi, hbudget⟩ := squareCut_data (by omega : 1 ≤ N)
  let U := S.filter fun n ↦ canonicalSquarePart n * canonicalSquarePart (n + h) ≤ squareCut N
  let V := S.filter fun n ↦ squareCut N < canonicalSquarePart n * canonicalSquarePart (n + h)
  have hU : (U.card : ℝ) ≤ (24 * h * T + (squareCut N : ℝ)) * (N : ℝ) ^ η := by
    apply hs N (by omega) H h T (squareCut N : ℝ) hH hhpos hT (Nat.cast_nonneg _) U
    intro n hnU
    obtain ⟨hnS, hnP⟩ := mem_filter.mp hnU
    exact ⟨(hS n hnS).1, (hS n hnS).2.1, (hS n hnS).2.2.1, (hS n hnS).2.2.2.1,
      (hS n hnS).2.2.2.2.1, (hS n hnS).2.2.2.2.2, by exact_mod_cast hnP⟩
  have hV : (V.card : ℝ) ≤ (16 * (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ η := by
    apply hl N (by omega) H h (16 * (N : ℝ) ^ (2 / 3 : ℝ)) hH hhpos hhwidth (by positivity) V
    intro n hnV
    obtain ⟨hnS, hnP⟩ := mem_filter.mp hnV
    obtain ⟨hnpos, hnlo, hnhi, hmhi, _hk₁, _hk₂⟩ := hS n hnS
    have hkprod := large_square_product H n (n + h) (squareCut N : ℝ) (4 * N)
      (16 * (N : ℝ) ^ (2 / 3 : ℝ)) (by exact_mod_cast hPpos) (by positivity) hnpos (by omega)
      (by exact_mod_cast (show n ≤ 4 * N by omega)) (by exact_mod_cast hmhi)
      (by have hp' : squareCut N ≤ canonicalSquarePart n * canonicalSquarePart (n + h) := hnP.le
          exact_mod_cast hp') hbudget
    refine ⟨by omega, by omega, 0, (h : ℤ), by simp, by simp, by exact_mod_cast (Ne.symm hhpos.ne'), ?_⟩
    simpa only [TwoSmallKernelFibres.largeKernel, LinearKernelFibres.value, add_zero,
      ← Nat.cast_add, Int.natAbs_natCast, Nat.cast_mul] using hkprod
  have hcard : (S.card : ℝ) ≤ U.card + V.card := by
    have hsub : S ⊆ U ∪ V := by
      intro n hnS
      by_cases hP : canonicalSquarePart n * canonicalSquarePart (n + h) ≤ squareCut N
      · exact mem_union_left _ (mem_filter.mpr ⟨hnS, hP⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hnS, lt_of_not_ge hP⟩)
    exact_mod_cast (card_le_card hsub).trans (card_union_le U V)
  have hsmall : 48 * (h : ℝ) ≤ (N : ℝ) ^ η := by
    have hh' := hh N (by omega)
    nlinarith only [hh', hhwidth]
  have hconst : 36 ≤ (N : ℝ) ^ η := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hc N (by omega)
  have hcoeff : 24 * (h : ℝ) * T + 18 * (N : ℝ) ^ (2 / 3 : ℝ) ≤
      (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ η := by
    have ht := mul_le_mul_of_nonneg_right hsmall hT
    have hr := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hn.le (2 / 3 : ℝ))
    nlinarith only [ht, hr, hT, Real.rpow_nonneg hn.le η, Real.rpow_nonneg hn.le (2 / 3 : ℝ)]
  calc
    _ ≤ (24 * h * T + 18 * (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ η := by
      nlinarith only [hcard, hU, hV, mul_le_mul_of_nonneg_right hPhi (Real.rpow_nonneg hn.le η)]
    _ ≤ ((T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ η) * (N : ℝ) ^ η :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hn.le η)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      dsimp [η]
      ring

end PaperP1.TwoSmallKernelElementaryUpper
