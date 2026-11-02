module

public import PaperP1.Asymptotics.ChannelMassPhaseEquivalent
public import PaperP1.Asymptotics.ChannelMainTermBounds

/-! # Uniform positive lower bounds for the moving omitted-height scalar phase -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelMassPhaseLower

open Finset PaperP1.FiniteChannelHierarchy PaperP1.ChannelPhaseConstants
  PaperP1.ChannelMassPhaseEquivalent

theorem heightMass_eq_main_terms (N L b : ℕ) (hN : 0 < N) :
    heightMass N L b = ∑ a ∈ numerators b, ChannelMainTermBounds.mainTerm N L a b := by
  rw [heightMass, heightSum, mul_sum]
  apply sum_congr rfl
  intro a _
  unfold nominalMean FiniteChannelHierarchy.weight ChannelMainTermBounds.mainTerm
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem uniform_phase_lower (C : ℝ) (b : ℕ) (hb : 3 ≤ b) :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      d * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ phaseMass N L b := by
  have ha : 0 < b - 1 := by omega
  have hab : b - 1 < b := by omega
  have hba : b < 2 * (b - 1) := by omega
  have hc := (ChannelMainTermBounds.constants_pos C ha (by omega : 0 < b) hba).1
  obtain ⟨NP, hNP, hphase⟩ := uniform_relative C b hb 1 (by norm_num)
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (10 * b ^ 3 + 1)
  refine ⟨ChannelMainTermBounds.lowerConstant C (b - 1) b / 2, by positivity,
    max NP NG, by omega, ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hLbig : 10 * b ^ 3 ≤ L := by have h := (hgeom N (by omega) L hband).2.1; omega
  have hnonneg (a : ℕ) (haMem : a ∈ numerators b) :
      0 ≤ ChannelMainTermBounds.mainTerm N L a b := by
    obtain ⟨haInt, hba', _⟩ := mem_filter.mp haMem
    obtain ⟨ha1, hab'⟩ := mem_Icc.mp haInt
    have ha' : 0 < a := by omega
    have hab'' : a < b := by omega
    have hc' := (ChannelMainTermBounds.constants_pos C ha' (by omega : 0 < b) hba').1
    exact (by positivity : 0 ≤ ChannelMainTermBounds.lowerConstant C a b * L *
      (N : ℝ) ^ (-1 + 1 / (b : ℝ))).trans
      (ChannelMainTermBounds.main_term_bounds hNtwo ha' hab'' hba' hLbig hband).1
  have hsingle := single_le_sum hnonneg (last_numerator b hb)
  have hheight : ChannelMainTermBounds.lowerConstant C (b - 1) b * L *
      (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ heightMass N L b := by
    rw [heightMass_eq_main_terms N L b (by omega)]
    exact (ChannelMainTermBounds.main_term_bounds hNtwo ha hab hba hLbig hband).1.trans hsingle
  have he := hphase N (by omega) L hband
  have habs := le_abs_self (heightMass N L b - phaseMass N L b)
  nlinarith only [he, habs, hheight]

theorem uniform_coarse_lower (C : ℝ) (b : ℕ) (hb : 3 ≤ b) :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → d / N ≤ phaseMass N L b := by
  obtain ⟨d, hd, NP, hNP, hlower⟩ := uniform_phase_lower C b hb
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨d, hd, max NP NG, by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpow : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (-1 + 1 / (b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      have hp : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
      linarith)
  calc
    _ = d * (N : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    _ ≤ d * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := mul_le_mul_of_nonneg_left hpow hd.le
    _ ≤ d * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
      have hp : 0 ≤ d * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hL1 hp]
    _ ≤ _ := hlower N (by omega) L hband

end PaperP1.ChannelMassPhaseLower
