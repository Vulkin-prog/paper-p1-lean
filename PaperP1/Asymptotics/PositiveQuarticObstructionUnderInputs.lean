module

public import PaperP1.Asymptotics.FourthCumulantIdentitiesUnderInputs
public import PaperP1.Asymptotics.PositiveSecondCumulant

/-! # The actual fourth Charlier coefficient is at least twice the square of alpha -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveQuarticObstructionUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FourthRunFactorialCumulant PaperP1.ConnectedWindowFamilies

theorem uniform_lower (C : ℝ) :
    ∃ p : FourthCumulantIdentitiesUnderInputs.Parameters,
      FourthCumulantIdentitiesUnderInputs.Hypotheses p (1 / 12) →
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
      let E := fourthFactorialCumulant (dyadicBlock N) L + 3 * α ^ 2
      2 * α ^ 2 ≤ E ∧ d * (L : ℝ) ^ 2 * (N : ℝ) ^ (-4 / 3 : ℝ) ≤ E := by
  obtain ⟨p, hp⟩ := FourthCumulantIdentitiesUnderInputs.article_16_1 C (1 / 12) (by norm_num)
  obtain ⟨d, hd, NA, _hNA, ha⟩ := PositiveSecondCumulant.uniform_lower C
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / d ^ 2) (-17 / 12) (1 / 12) (by norm_num)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NQ, _hNQ, hq⟩ := hp hgeo
  refine ⟨2 * d ^ 2, by positivity, max 2 (max NA (max NL (max NF NQ))), by omega, ?_⟩
  intro N hN L hband
  dsimp only
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hl N (by omega) L hband).2.2.1; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  have hα := ha N (by omega) L hband
  have hbase : d * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ α := by
    have h := mul_le_mul_of_nonneg_right hL1 (mul_nonneg hd.le (Real.rpow_nonneg hn.le (-2 / 3)))
    apply le_trans _ hα
    nlinarith only [h]
  have hsq : d ^ 2 * (N : ℝ) ^ (-4 / 3 : ℝ) ≤ α ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ d * (N : ℝ) ^ (-2 / 3 : ℝ)) hbase 2
    rw [mul_pow, ← Real.rpow_mul_natCast hn.le] at h
    rw [show (-2 / 3 : ℝ) * (2 : ℕ) = -4 / 3 by norm_num] at h
    exact h
  have herr : (N : ℝ) ^ (-17 / 12 : ℝ) ≤ α ^ 2 := by
    have h := hf N (by omega)
    rw [show (-17 / 12 : ℝ) + 1 / 12 = -4 / 3 by ring] at h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg d)
    have heq : d ^ 2 * ((1 / d ^ 2) * (N : ℝ) ^ (-17 / 12 : ℝ)) =
        (N : ℝ) ^ (-17 / 12 : ℝ) := by field_simp
    rw [heq] at hmul
    exact hmul.trans hsq
  obtain ⟨hpos, _hfirst, _hsecond, hfourth⟩ := hq N (by omega) L hband
  have he : 2 * α ^ 2 ≤ fourthFactorialCumulant (dyadicBlock N) L + 3 * α ^ 2 := by
    have hlow := (abs_le.mp hfourth).1
    rw [show (-3 / 2 : ℝ) + 1 / 12 = -17 / 12 by ring] at hlow
    change _ ≤ fourthFactorialCumulant (dyadicBlock N) L + 3 * α ^ 2 -
      (3 * α ^ 2 + 24 * CompatibleActivitySplit.positive L (connectedFamilies (dyadicBlock N) L 4)) at hlow
    nlinarith only [hlow, herr, hpos]
  refine ⟨he, ?_⟩
  have hfull := pow_le_pow_left₀ (by positivity : 0 ≤ d * L * (N : ℝ) ^ (-2 / 3 : ℝ)) hα 2
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hn.le] at hfull
  rw [show (-2 / 3 : ℝ) * (2 : ℕ) = -4 / 3 by norm_num] at hfull
  nlinarith only [hfull, he]

end PaperP1.PositiveQuarticObstructionUnderInputs
