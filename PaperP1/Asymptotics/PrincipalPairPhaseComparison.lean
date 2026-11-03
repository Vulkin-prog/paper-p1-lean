module

public import PaperP1.Asymptotics.ChannelMassPhaseLower
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Exact principal phases and uniform control of the smaller channel and power errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalPairPhaseComparison

open Finset PaperP1.FiniteChannelHierarchy PaperP1.ChannelPhaseConstants
  PaperP1.ChannelMassPhaseEquivalent PaperP1.ChannelMassPhaseLower

theorem height_three (N L : ℕ) (hN : 0 < N) :
    heightMass N L 3 = ChannelMainTermBounds.mainTerm N L 2 3 := by
  rw [heightMass_eq_main_terms N L 3 hN, numerators_three, sum_singleton]

theorem height_four (N L : ℕ) (hN : 0 < N) :
    heightMass N L 4 = ChannelMainTermBounds.mainTerm N L 3 4 := by
  rw [heightMass_eq_main_terms N L 4 hN, numerators_four, sum_singleton]

theorem mainTerm_eq_nominal (N L a b : ℕ) (hN : 0 < N) :
    ChannelMainTermBounds.mainTerm N L a b =
      (nominalMean N L) ^ 2 / N * (ActualSourceTranslations.coefficient a b : ℝ) *
        (ChannelSumIdentity.signed L a b : ℤ) := by
  unfold ChannelMainTermBounds.mainTerm nominalMean
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem whole_first_channel (N L : ℕ) (hN : 0 < N) :
    ChannelMainTermBounds.mainTerm N L 2 3 =
      (nominalMean N L) ^ 2 / (3 * N) * (ChannelSumIdentity.signed L 2 3 : ℤ) := by
  rw [mainTerm_eq_nominal N L 2 3 hN]
  have hc : (ActualSourceTranslations.coefficient 2 3 : ℝ) = 1 / 3 := by
    norm_num [ActualSourceTranslations.coefficient]
  rw [hc]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem phase_three (N L : ℕ) :
    phaseMass N L 3 = (((L % 3 : ℕ) : ℝ) + 2) /
      (18 * (2 : ℝ) ^ (((L % 3 : ℕ) : ℝ) / 3)) *
      (nominalMean N L) ^ (5 / 3 : ℝ) * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
  rw [phaseMass, phaseConstant_three]
  norm_num only [Nat.cast_ofNat]

theorem phase_four (N L : ℕ) :
    phaseMass N L 4 = (((L % 4 : ℕ) : ℝ) + 3) /
      (24 * (2 : ℝ) ^ (((L % 4 : ℕ) : ℝ) / 4)) *
      (nominalMean N L) ^ (7 / 4 : ℝ) * L * (N : ℝ) ^ (-3 / 4 : ℝ) := by
  rw [phaseMass, phaseConstant_four]
  norm_num only [Nat.cast_ofNat]

theorem power_error_negligible (C θ : ℝ) (b : ℕ) (hb : 3 ≤ b)
    (hθ : θ < -1 + 1 / (b : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ θ ≤ ε * phaseMass N L b := by
  obtain ⟨d, hd, ND, _hND, hlower⟩ := uniform_phase_lower C b hb
  have hprod : 0 < ε * d := mul_pos hε hd
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / (ε * d)) θ
    (-1 + 1 / (b : ℝ) - θ) (by linarith)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max ND (max NF NG)), by omega, ?_⟩
  intro N hN L hband
  have hL : (1 : ℝ) ≤ L := by
    have h := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (show 1 ≤ L by omega)
  have hl := hlower N (by omega) L hband
  have hphase : d * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ phaseMass N L b := by
    have h := mul_le_mul_of_nonneg_left hL
      (by positivity : (0 : ℝ) ≤ d * (N : ℝ) ^ (-1 + 1 / (b : ℝ)))
    nlinarith only [h, hl]
  have hfactor := hf N (by omega)
  rw [show θ + (-1 + 1 / (b : ℝ) - θ) = -1 + 1 / (b : ℝ) by ring] at hfactor
  have hbudget := mul_le_mul_of_nonneg_left hfactor hprod.le
  rw [← mul_assoc, mul_one_div_cancel hprod.ne', one_mul] at hbudget
  exact hbudget.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hphase hε.le)

theorem next_channel_negligible (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |ChannelMainTermBounds.mainTerm N L 3 4| ≤ ε * phaseMass N L 3 := by
  obtain ⟨d, hd, ND, _hND, hlower⟩ := uniform_phase_lower C 3 (by decide)
  let K := ChannelMainTermBounds.upperConstant C 3 4
  have hprod : 0 < ε * d := mul_pos hε hd
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (K / (ε * d)) (-3 / 4) (1 / 12) (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (10 * 4 ^ 3 + 1)
  refine ⟨max 2 (max ND (max NF NG)), by omega, ?_⟩
  intro N hN L hband
  have hLbig : 10 * (4 : ℕ) ^ 3 ≤ L := by have h := (hg N (by omega) L hband).2.1; omega
  have hm := ChannelMainTermBounds.main_term_bounds (by omega : 2 ≤ N) (by decide : 0 < 3)
    (by decide : 3 < 4) (by decide : 4 < 2 * 3) hLbig hband
  norm_num only [Nat.cast_ofNat] at hm
  simp only [← neg_div] at hm
  have hc := (ChannelMainTermBounds.constants_pos C (by decide : 0 < 3) (by decide : 0 < 4)
    (by decide : 4 < 2 * 3)).1
  have hmainpos : 0 ≤ ChannelMainTermBounds.mainTerm N L 3 4 :=
    (by positivity : 0 ≤ ChannelMainTermBounds.lowerConstant C 3 4 * L * (N : ℝ) ^ (-3 / 4 : ℝ)).trans hm.1
  have hl := hlower N (by omega) L hband
  norm_num only [Nat.cast_ofNat] at hl
  simp only [← neg_div] at hl
  have hfactor := hf N (by omega)
  norm_num only [show (-3 / 4 : ℝ) + 1 / 12 = -2 / 3 by norm_num] at hfactor
  simp only [← neg_div] at hfactor
  have hbudget : K * (N : ℝ) ^ (-3 / 4 : ℝ) ≤ (ε * d) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    have heq : K / (ε * d) * (N : ℝ) ^ (-3 / 4 : ℝ) =
        (K * (N : ℝ) ^ (-3 / 4 : ℝ)) / (ε * d) := by ring
    rw [heq] at hfactor
    have h := (div_le_iff₀ hprod).mp hfactor
    simpa only [mul_comm] using h
  rw [abs_of_nonneg hmainpos]
  calc
    _ ≤ K * L * (N : ℝ) ^ (-3 / 4 : ℝ) := hm.2
    _ = (K * (N : ℝ) ^ (-3 / 4 : ℝ)) * L := by ring
    _ ≤ ((ε * d) * (N : ℝ) ^ (-2 / 3 : ℝ)) * L :=
      mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
    _ = ε * (d * L * (N : ℝ) ^ (-2 / 3 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hε.le

theorem ratio_bound {x y ε : ℝ} (hy : 0 < y) (herror : |x - y| ≤ ε * y) :
    |x / y - 1| ≤ ε := by
  have heq : x / y - 1 = (x - y) / y := by field_simp
  rw [heq, abs_div, abs_of_pos hy]
  exact (div_le_iff₀ hy).mpr herror

end PaperP1.PrincipalPairPhaseComparison
