module

public import PaperP1.Arithmetic.LogBudgetEuler
public import PaperP1.Arithmetic.OldValuePrimeBudget
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # The actual old-source Euler factor, including all primes up to the square-of-width cutoff, is uniformly subpower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentExposurePrimePool

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.DefectCounting PaperP1.SmoothSquarefreeCount
  PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget PaperP1.CriticalBandScale

def cutoff (B : ℕ) : ℕ := 64 * B ^ 2

def basePrimes (A : Finset ℕ) (L : ℕ) : Finset ℕ :=
  primePool (rawValues A L) (L + 1) ∪ smallPrimesUpTo (cutoff (L + 1))

def baseEuler (A : Finset ℕ) (L : ℕ) : ℝ := eulerProduct (basePrimes A L) (1 / 2)

theorem base_prime (A : Finset ℕ) (L p : ℕ) (hp : p ∈ basePrimes A L) : Nat.Prime p := by
  rcases mem_union.mp hp with hp | hp
  · exact primePool_prime _ _ _ hp
  · exact (mem_smallPrimesUpTo.mp hp).1

theorem logarithmic_budget {A : Finset ℕ} {N L s : ℕ} (hA : A ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hLN : L ≤ N) (hs : A.card ≤ s) :
    (∑ p ∈ basePrimes A L, Real.log p) ≤
      (cutoff (L + 1) : ℝ) * Real.log 4 + ((L + 1 : ℕ) : ℝ) * Real.log 4 +
        (s : ℝ) * (L + 1) * Real.log (3 * N : ℕ) := by
  have hOld := raw_primePool_log_sum_le hA hN hLN hs
  have hSmall := SmallPrimeBudget.prime_log_sum_le (cutoff (L + 1))
  have h := log_sum_union_le (primePool (rawValues A L) (L + 1)) (smallPrimesUpTo (cutoff (L + 1)))
  exact h.trans (by linarith only [hOld, hSmall])

theorem uniform_bound (s : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ s → baseEuler A L ≤ (N : ℝ) ^ ε := by
  let c := WeightedPrimeSum.smallPrimeConstant
  let H := 8 * (c + Real.log 4) * upperScale + (1 + 2 * (s : ℝ)) / 8
  let K := max 1 (H / ε)
  let Bmin := ⌈Real.exp K⌉₊
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C Bmin
  refine ⟨max 4 NG, by omega, ?_⟩
  intro N hN L hband A hA hs
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hnlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  let B := L + 1
  let Y := cutoff B
  have hgN := hg N (by omega) L hband
  have hB2 : 2 ≤ B := hgN.2.2.1
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hY2 : 2 ≤ Y := by dsimp [Y, cutoff]; nlinarith only [hB2]
  have hlogY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY2)
  have hLN : L ≤ N := by have h := hgN.2.2.2.1; omega
  have hwidth : (B : ℝ) ≤ upperScale * Real.log N := hgN.2.2.2.2.2
  have hexpB : Real.exp K ≤ B := (Nat.le_ceil _).trans (by exact_mod_cast hgN.2.1)
  have hlogB : K ≤ Real.log B := by
    have h := Real.log_le_log (Real.exp_pos K) hexpB
    simpa only [Real.log_exp] using h
  have hBY : B ≤ Y := by dsimp [Y, cutoff]; nlinarith only [hB2]
  have hKlog : K ≤ Real.log Y := hlogB.trans (Real.log_le_log hBpos (by exact_mod_cast hBY))
  have hH : H ≤ ε * Real.log Y := by
    have h := (div_le_iff₀ hε).mp ((le_max_right 1 (H / ε)).trans hKlog)
    linarith only [h]
  have hroot : Real.sqrt (Y : ℝ) = 8 * B := by
    have heq : (Y : ℝ) = (8 * (B : ℝ)) ^ 2 := by dsimp [Y, cutoff]; push_cast; ring
    rw [heq, Real.sqrt_sq (by positivity)]
  have hlog4 : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hn4
  have hlog3N : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h3N : (3 * N : ℕ) ≤ N ^ 2 := by nlinarith only [show 4 ≤ N by omega]
    have hpos3 : (0 : ℝ) < (3 * N : ℕ) := by exact_mod_cast (show 0 < 3 * N by omega)
    have hupper3 : ((3 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast h3N
    have h := Real.log_le_log hpos3 hupper3
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have hc : 0 ≤ c + Real.log 4 := by
    dsimp [c, WeightedPrimeSum.smallPrimeConstant]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith only [hlog]
  have hNum : 8 * (c + Real.log 4) * B + Real.log 4 / 8 +
      (s : ℝ) * Real.log (3 * N : ℕ) / 8 ≤ H * Real.log N := by
    have h₁ := mul_le_mul_of_nonneg_left hwidth (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hc)
    have h₂ := mul_le_mul_of_nonneg_left hlog3N (by positivity : 0 ≤ (s : ℝ) / 8)
    dsimp [H]
    nlinarith only [h₁, h₂, hlog4]
  have hExponent : c * Real.sqrt Y / Real.log Y +
      ((Y : ℝ) * Real.log 4 + (B : ℝ) * Real.log 4 +
        (s : ℝ) * B * Real.log (3 * N : ℕ)) / (Real.sqrt Y * Real.log Y) ≤ ε * Real.log N := by
    have heq : c * Real.sqrt Y / Real.log Y +
        ((Y : ℝ) * Real.log 4 + (B : ℝ) * Real.log 4 +
          (s : ℝ) * B * Real.log (3 * N : ℕ)) / (Real.sqrt Y * Real.log Y) =
        (8 * (c + Real.log 4) * B + Real.log 4 / 8 +
          (s : ℝ) * Real.log (3 * N : ℕ) / 8) / Real.log Y := by
      rw [hroot]
      dsimp [Y, cutoff]
      push_cast
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ hlogY).mpr
    have hmul := mul_le_mul_of_nonneg_right hH hnlog
    nlinarith only [hNum, hmul]
  calc
    _ ≤ Real.exp (c * Real.sqrt Y / Real.log Y +
        ((Y : ℝ) * Real.log 4 + (B : ℝ) * Real.log 4 +
          (s : ℝ) * B * Real.log (3 * N : ℕ)) / (Real.sqrt Y * Real.log Y)) :=
      LogBudgetEuler.finite_bound (basePrimes A L) (base_prime A L) Y hY2 _ (by
        simpa only [Y, B, Nat.cast_add, Nat.cast_one] using logarithmic_budget hA (by omega) hLN hs)
    _ ≤ Real.exp (ε * Real.log N) := Real.exp_le_exp.mpr hExponent
    _ = _ := by rw [Real.rpow_def_of_pos hn]; congr 1; ring

end PaperP1.IndependentExposurePrimePool
