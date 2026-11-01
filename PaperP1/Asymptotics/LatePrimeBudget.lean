module

public import PaperP1.Arithmetic.LateWindowPrimes
public import PaperP1.Asymptotics.ScaledPrimeCounts

/-! # The proved 17/12 prime budget for actual upper-half raw values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePrimeBudget

open Finset Filter PaperP1.DefectCounting PaperP1.LocalDefectBound
  PaperP1.LateWindowPrimes PaperP1.ConditionalWindowRank

def envelope (N : ℕ) : ℝ :=
  (primeCount (2 * N / 3) : ℝ) +
    ((primeCount N : ℝ) - primeCount (3 * N / 4 - 1)) +
    ((primeCount (2 * N) : ℝ) - primeCount (3 * N / 2 - 1))

theorem cover_card_le (N : ℕ) : ((cover N).card : ℝ) ≤ envelope N := by
  have hsmall := card_le_card (smallPrimes_mono (show 3 * N / 4 - 1 ≤ N by omega))
  have hlarge := card_le_card (smallPrimes_mono (show 3 * N / 2 - 1 ≤ 2 * N by omega))
  have hsmall' : primeCount (3 * N / 4 - 1) ≤ primeCount N := hsmall
  have hlarge' : primeCount (3 * N / 2 - 1) ≤ primeCount (2 * N) := hlarge
  have h := Nat.cast_le (α := ℝ).mpr (cover_card N)
  simpa only [Nat.cast_add, Nat.cast_sub hsmall', Nat.cast_sub hlarge', envelope] using h

theorem envelope_ratio_tendsto :
    Tendsto (fun N : ℕ ↦ envelope N * Real.log N / N) atTop (nhds (17 / 12 : ℝ)) := by
  have hlow := ScaledPrimeCounts.prime_count_divided_shifted 2 3 0 (by norm_num) (by norm_num)
  have hmiddle := ScaledPrimeCounts.prime_count_divided_shifted 1 1 0 (by norm_num) (by norm_num)
  have hmiddleLo := ScaledPrimeCounts.prime_count_divided_shifted 3 4 1 (by norm_num) (by norm_num)
  have hhigh := ScaledPrimeCounts.prime_count_divided_shifted 2 1 0 (by norm_num) (by norm_num)
  have hhighLo := ScaledPrimeCounts.prime_count_divided_shifted 3 2 1 (by norm_num) (by norm_num)
  have h := (hlow.add (hmiddle.sub hmiddleLo)).add (hhigh.sub hhighLo)
  norm_num only [Nat.sub_zero, Nat.div_one, Nat.one_mul, Nat.cast_ofNat, one_div] at h
  convert h using 1
  funext N
  unfold envelope
  ring

theorem cover_bound_eventually (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      ((cover N).card : ℝ) ≤ (17 / 12 + η) * N / Real.log N := by
  obtain ⟨Nlim, hNlim⟩ := eventually_atTop.mp
    (envelope_ratio_tendsto.eventually (eventually_lt_nhds (by linarith : (17 / 12 : ℝ) < 17 / 12 + η)))
  refine ⟨max 3 Nlim, by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h := (div_le_iff₀ hn).mp (hNlim N (by omega)).le
  exact (cover_card_le N).trans ((le_div_iff₀ hlog).mpr h)

theorem oldPrimes_bound_eventually (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ R : Finset ℕ,
      (∀ n ∈ R, 3 * N ≤ 2 * n ∧ n < 2 * N) →
        ((oldPrimes R).card : ℝ) ≤ (17 / 12 + η) * N / Real.log N := by
  obtain ⟨N₀, hN₀, hbound⟩ := cover_bound_eventually η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN R hR
  have hcard : ((oldPrimes R).card : ℝ) ≤ (cover N).card := by
    exact_mod_cast card_le_card (oldPrimes_subset hR)
  exact hcard.trans (hbound N hN)

end PaperP1.LatePrimeBudget
