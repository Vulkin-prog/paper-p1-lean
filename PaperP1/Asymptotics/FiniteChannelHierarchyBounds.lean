module

public import PaperP1.Arithmetic.FiniteChannelHierarchy
public import PaperP1.Asymptotics.ChannelMainTermBounds
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Positive, vanishing finite-height explicit coefficients without a pair profile

The height is fixed before the threshold. These statements use the literal
finite signed channel polynomials, without a count-law or cumulant estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteChannelHierarchyBounds

open Finset Filter PaperP1.FiniteChannelHierarchy PaperP1.CriticalBandScale

def upperConstant (C : ℝ) (h : ℕ) : ℝ :=
  1 + ∑ z ∈ channels h, max 0 (ChannelMainTermBounds.upperConstant C z.2 z.1)

theorem upperConstant_pos (C : ℝ) (h : ℕ) : 0 < upperConstant C h := by
  have hs : 0 ≤ ∑ z ∈ channels h, max 0 (ChannelMainTermBounds.upperConstant C z.2 z.1) :=
    sum_nonneg (fun _ _ ↦ le_max_left _ _)
  unfold upperConstant
  linarith

theorem coefficient_eq_main_terms (N L h : ℕ) (hN : 0 < N) :
    coefficient N L h = ∑ z ∈ channels h, ChannelMainTermBounds.mainTerm N L z.2 z.1 := by
  rw [coefficient, truncatedSum_eq_channels, mul_sum]
  apply sum_congr rfl
  intro z _
  unfold nominalMean weight ChannelMainTermBounds.mainTerm
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem uniform_bounds (C : ℝ) (h : ℕ) (hh : 3 ≤ h) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ChannelMainTermBounds.lowerConstant C 2 3 * L * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ coefficient N L h ∧
        coefficient N L h ≤ upperConstant C h * L * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (10 * h ^ 3 + 1)
  refine ⟨max 2 NG, by omega, ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hLbig : 10 * h ^ 3 ≤ L := by have h := (hgeom N (by omega) L hband).2.1; omega
  have hdata (z : Σ _b : ℕ, ℕ) (hz : z ∈ channels h) :
      0 ≤ ChannelMainTermBounds.mainTerm N L z.2 z.1 ∧
        ChannelMainTermBounds.mainTerm N L z.2 z.1 ≤
          max 0 (ChannelMainTermBounds.upperConstant C z.2 z.1) * L * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    obtain ⟨hb3, _hbh, ha1, hab, hba, _hcop⟩ := mem_channels.mp hz
    have ha : 0 < z.2 := by omega
    have hb : 0 < z.1 := by omega
    have hLb : 10 * z.1 ^ 3 ≤ L :=
      (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left _hbh 3)).trans hLbig
    have ht := ChannelMainTermBounds.main_term_bounds hNtwo ha hab hba hLb hband
    have hc := (ChannelMainTermBounds.constants_pos C ha hb hba).1
    have hpow : (N : ℝ) ^ (-1 + 1 / (z.1 : ℝ)) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1
      have hr := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
        (by exact_mod_cast hb3 : (3 : ℝ) ≤ z.1)
      linarith
    refine ⟨(by positivity : 0 ≤ ChannelMainTermBounds.lowerConstant C z.2 z.1 * L *
      (N : ℝ) ^ (-1 + 1 / (z.1 : ℝ))).trans ht.1, ?_⟩
    calc
      _ ≤ _ := ht.2
      _ ≤ max 0 (ChannelMainTermBounds.upperConstant C z.2 z.1) * L *
          (N : ℝ) ^ (-1 + 1 / (z.1 : ℝ)) := by gcongr; exact le_max_right _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  rw [coefficient_eq_main_terms N L h (by omega)]
  constructor
  · have hmem := leading_channel_mem hh
    have hsingle := single_le_sum (fun z hz ↦ (hdata z hz).1) hmem
    have hLb : 10 * (3 : ℕ) ^ 3 ≤ L :=
      (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hh 3)).trans hLbig
    have hlower := (ChannelMainTermBounds.main_term_bounds hNtwo
      (by norm_num : 0 < (2 : ℕ)) (by norm_num : (2 : ℕ) < 3)
      (by norm_num : (3 : ℕ) < 2 * 2) hLb hband).1
    have hlower' : ChannelMainTermBounds.lowerConstant C 2 3 * L * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤
        ChannelMainTermBounds.mainTerm N L 2 3 := by
      simpa only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 3 = -2 / 3 by ring] using hlower
    exact hlower'.trans hsingle
  · calc
      _ ≤ ∑ z ∈ channels h, max 0 (ChannelMainTermBounds.upperConstant C z.2 z.1) * L *
          (N : ℝ) ^ (-(2 : ℝ) / 3) := sum_le_sum (fun z hz ↦ (hdata z hz).2)
      _ = (∑ z ∈ channels h, max 0 (ChannelMainTermBounds.upperConstant C z.2 z.1)) * L *
          (N : ℝ) ^ (-(2 : ℝ) / 3) := by simp only [sum_mul]
      _ ≤ _ := by
        unfold upperConstant
        have hp : 0 ≤ (L : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
        nlinarith only [hp]

theorem uniform_positive (C : ℝ) (h : ℕ) (hh : 3 ≤ h) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 < coefficient N L h := by
  obtain ⟨NA, hNA, hbound⟩ := uniform_bounds C h hh
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  have hc := (ChannelMainTermBounds.constants_pos C (by norm_num : 0 < (2 : ℕ))
    (by norm_num : 0 < (3 : ℕ)) (by norm_num : (3 : ℕ) < 2 * 2)).1
  refine ⟨max NA NG, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (mul_pos (mul_pos hc (by exact_mod_cast hL)) (Real.rpow_pos_of_pos hn _)).trans_le
    (hbound N (by omega) L hband).1

theorem uniform_power_bound (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      coefficient N L h ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  let K := upperConstant C h
  have hK : 0 < K := upperConstant_pos C h
  obtain ⟨NA, hNA, hbound⟩ := uniform_bounds C h hh
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NF, hfactor⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le K 1 ε hε
  refine ⟨max NA (max NG NF), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨_, _, _, _, _, hB⟩ := hgeom N (by omega) L hband
  have hpoly := hfactor N (by omega) L hB
  have hpoly' : K * ((L : ℝ) + 1) ≤ (N : ℝ) ^ ε := by
    simpa only [pow_one, abs_of_nonneg (by positivity : 0 ≤ K * ((L : ℝ) + 1))] using hpoly
  have hKL : K * (L : ℝ) ≤ (N : ℝ) ^ ε := by linarith only [hpoly', hK]
  calc
    _ ≤ K * L * (N : ℝ) ^ (-(2 : ℝ) / 3) := (hbound N (by omega) L hband).2
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_small (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → coefficient N L h ≤ δ := by
  obtain ⟨NA, hNA, hbound⟩ := uniform_power_bound C h hh (1 / 6) (by norm_num)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨NT, htail⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hδ))
  refine ⟨max NA NT, by omega, ?_⟩
  intro N hN L hband
  have hb := hbound N (by omega) L hband
  norm_num only [show -(2 : ℝ) / 3 + 1 / 6 = -(1 / 2) by ring] at hb
  exact hb.trans (htail N (by omega)).le

theorem nominal_bounds {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    ((2 : ℝ) ^ C)⁻¹ ≤ nominalMean N L ∧ nominalMean N L ≤ (2 : ℝ) ^ C := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  constructor
  · calc
      _ = (N : ℝ) * (((2 : ℝ) ^ C)⁻¹ / N) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (CriticalChannelPowers.nominal_lower hN hband) hn.le
  · calc
      _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound hN hband) hn.le
      _ = _ := by field_simp

end PaperP1.FiniteChannelHierarchyBounds
