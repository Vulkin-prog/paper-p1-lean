module

public import PaperP1.Asymptotics.SignedDyadicCostLower
public import PaperP1.Asymptotics.ElementaryCleanPivotLower
public import PaperP1.Asymptotics.AnchoredCostErrorScale
public import PaperP1.Asymptotics.LogFifthPivotCutoff

/-! # An elementary power-scale lower bound for the specified signed forcing

The literal clean population, reciprocal mass, collisions and both
exceptional losses are discharged. The upper cost estimate of T19.16
is a separate obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementarySignedCostLower

open Finset
  PaperP1.CleanBoundaryReciprocal PaperP1.CleanPivotPairs PaperP1.OddPrimePivot
  PaperP1.SignedPrivateDyadicField PaperP1.SignedExactWords PaperP1.ForcingExceptionalSets

theorem uniform_actual_lower (D : ℝ) (hD : 0 ≤ D) (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 20) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E : ℕ, ∀ hL : 1 ≤ L,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      (signedMarkRate L 0) ^ 2 * ((N : ℝ) ^ 2 / 4) *
        (N : ℝ) ^ (-δ) ≤
          PaperP1.SignedPrivateField.cost (data (E := E) (by omega : 2 ≤ N) hL) := by
  obtain ⟨NF, hF⟩ := PaperP1.SignedDyadicCostLower.uniform_actual_lower D hD (1 / 40) (by norm_num)
  obtain ⟨NS, _hNS, hS⟩ := PaperP1.ElementaryCleanPivotLower.uniform_lower D hD δ hδ
  obtain ⟨NY, hY⟩ := PaperP1.LogFifthPivotCutoff.uniform_data D (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨NE, hE⟩ := PaperP1.AnchoredCostErrorScale.uniform_errors D (1 / 20) 1 hD (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨NP, hP⟩ := HalfCountSchedule.factor_absorption 8 (39 / 20) (1 / 20 - δ) (by linarith only [hδsmall])
  refine ⟨max NF (max NS (max NY (max NE NP))), ?_⟩
  intro N hN L E hL hwidth
  let Y := PaperP1.LogFifthPivotCutoff.cutoff N
  let J := sources N (L + E + 2) Y
  let c : ℝ := ((L + 1 : ℕ) : ℝ) * (L + 2 : ℕ) + 1
  let F := (N : ℝ) ^ (-δ)
  have hsuccess : L + 1 + 1 = L + 2 := by omega
  obtain ⟨hYbig, hYpos, hcollision, _hcleY, hYupper⟩ := hY N (by omega) (L + E + 2) (L + 1) hwidth (by omega)
  rw [hsuccess] at hcollision
  have hYcut : pivotCutoff L E ≤ Y := by exact hYbig
  have hcost := hF N (by omega) L E Y hL hwidth hYcut hYupper J
    (sources_subset _ _ _) (fun j hj ↦ sources_good hj)
  have hsource := hS N (by omega) (L + E + 2) Y (by omega) hwidth hYpos hYupper
  have hsource' : (N : ℝ) / 2 * F ≤ reciprocalSum J largestOddPrime := by
    have hid : (N : ℝ) ^ (1 - δ) = (N : ℝ) * F := by
      calc
        _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-δ) := by
          rw [← Real.rpow_add (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))]
          congr 1
        _ = _ := by rw [Real.rpow_one]
    change (N : ℝ) ^ (1 - δ) ≤ reciprocalSum J largestOddPrime at hsource
    rw [hid] at hsource
    have hnon : 0 ≤ (N : ℝ) * F := by positivity
    linarith only [hsource, hnon]
  have hcard : (J.card : ℝ) ≤ N := by
    exact_mod_cast (card_le_card (sources_subset N (L + E + 2) Y)).trans (boundaryBlock_card_le N)
  have hKwidth : ((L + 1 + 1 : ℕ) : ℝ) ≤ D * Real.log N := by
    have hh : ((L + 1 + 1 : ℕ) : ℝ) ≤ ((L + E + 2 : ℕ) : ℝ) := by exact_mod_cast (show L + 1 + 1 ≤ L + E + 2 by omega)
    exact hh.trans hwidth
  have herrors := (hE N (by omega) (L + 1) hKwidth).2
  rw [hsuccess, show PaperP1.AnchoredCostErrorScale.errorExponent (1 / 20) = 1 / 40 by
    norm_num [PaperP1.AnchoredCostErrorScale.errorExponent]] at herrors
  norm_num only [show (2 : ℝ) - 1 / 20 = 39 / 20 by norm_num, one_mul] at herrors
  have hpower := hP N (by omega)
  rw [show (39 / 20 : ℝ) + (1 / 20 - δ) = 2 - δ by ring] at hpower
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpower' : (N : ℝ) ^ (39 / 20 : ℝ) ≤ (1 / 8) * (N : ℝ) ^ 2 * F := by
    have hid : (N : ℝ) ^ (2 - δ) = (N : ℝ) ^ 2 * F := by
      dsimp only [F]
      rw [← Real.rpow_two, ← Real.rpow_add hnpos]
      congr 1
    rw [hid] at hpower
    linarith only [hpower]
  have hcpos : 0 ≤ c + 1 := by dsimp [c]; positivity
  have hcarderror := mul_le_mul_of_nonneg_left hcard hcpos
  have hrest : (c + 1) * J.card + (N : ℝ) ^ (19 / 10 + 1 / 40 : ℝ) +
      (N : ℝ) ^ (3 / 2 + 1 / 40 : ℝ) ≤ (1 / 8) * (N : ℝ) ^ 2 * F := by
    have he' : (c + 1) * N + (N : ℝ) ^ (19 / 10 + 1 / 40 : ℝ) +
        (N : ℝ) ^ (3 / 2 + 1 / 40 : ℝ) ≤ (N : ℝ) ^ (39 / 20 : ℝ) := by
      simpa only [c, show (19 : ℝ) / 10 + 1 / 40 = 77 / 40 by norm_num,
        show (3 : ℝ) / 2 + 1 / 40 = 61 / 40 by norm_num] using herrors
    dsimp [F]
    linarith only [hcarderror, he', hpower']
  have hcol : c / Y ≤ 1 / 4 := hcollision
  have hcoef : 3 / 4 ≤ 1 - c / Y := by linarith only [hcol]
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hrec : 0 ≤ reciprocalSum J largestOddPrime := reciprocalSum_nonneg _ _
  have hlead : (3 / 8) * (N : ℝ) ^ 2 * F ≤ (1 - c / Y) * N * reciprocalSum J largestOddPrime := by
    have hm := mul_le_mul hcoef (mul_le_mul_of_nonneg_left hsource' hn)
      (by dsimp [F]; positivity : (0 : ℝ) ≤ (N : ℝ) * ((N : ℝ) / 2 * F))
      (by linarith only [hcoef] : 0 ≤ 1 - c / Y)
    change (3 / 4) * ((N : ℝ) * ((N : ℝ) / 2 * F)) ≤
      (1 - c / Y) * ((N : ℝ) * reciprocalSum J largestOddPrime) at hm
    nlinarith only [hm]
  have hbracket : ((N : ℝ) ^ 2 / 4) * F ≤
      (N : ℝ) * reciprocalSum J largestOddPrime - J.card -
        c * (((N : ℝ) / Y) * reciprocalSum J largestOddPrime + J.card) -
        (N : ℝ) ^ (19 / 10 + 1 / 40 : ℝ) - (N : ℝ) ^ (3 / 2 + 1 / 40 : ℝ) := by
    have hid : (N : ℝ) * reciprocalSum J largestOddPrime - J.card -
        c * (((N : ℝ) / Y) * reciprocalSum J largestOddPrime + J.card) =
        (1 - c / Y) * N * reciprocalSum J largestOddPrime - (c + 1) * J.card := by ring
    rw [hid]
    nlinarith only [hlead, hrest]
  have hw := mul_le_mul_of_nonneg_left hbracket (sq_nonneg (signedMarkRate L 0))
  have hh := hw.trans hcost
  simpa only [mul_assoc] using hh

end PaperP1.ElementarySignedCostLower
