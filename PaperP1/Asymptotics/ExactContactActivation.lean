module

public import PaperP1.Model.ExactContactEdges
public import PaperP1.Model.ActiveFamilyCover
public import PaperP1.Asymptotics.ActiveEdgeMoments
public import PaperP1.Asymptotics.ContactSeedKernel
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Exact-contact seed mass and activation probability have exponent -1 unconditionally -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactContactActivation

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ExactContactEdges

theorem uniform_regular_union_count (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) / 2 ≤ (regularUnionStarts N L).card := by
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NI, hi⟩ := RegularStarts.card_irregularStarts_le_rpow_eventually
    (2 * CriticalBandScale.upperScale) (mul_nonneg (by norm_num) CriticalBandScale.upperScale_pos.le) (1 / 2) (by norm_num)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 4 (by norm_num) 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (1 / 2) (1 / 2) (by norm_num)
  refine ⟨max 2 (max NS (max NI (max NL NF))), by omega, ?_⟩
  intro N hN L hband
  have hB := (hs N (by omega) L hband).2
  have hdouble : ((2 * L + 1 : ℕ) : ℝ) ≤ (2 * CriticalBandScale.upperScale) * Real.log N := by
    have htw : ((2 * L + 1 : ℕ) : ℝ) ≤ 2 * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 * L + 1 ≤ 2 * (L + 1) by omega)
    nlinarith only [htw, hB]
  have hirr := hi N (by omega) (2 * L) hdouble
  have hfour : 4 * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  have hLN : L ≤ N := by omega
  have hcount := regular_union_count hLN
  have hc : (N : ℝ) - L ≤ (regularUnionStarts N L).card + (RegularStarts.irregularStarts N (2 * L)).card := by
    exact_mod_cast (show N - L ≤ _ from hcount)
  have hfR : 4 * (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
    simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring, Real.rpow_one] using hf N (by omega)
  have hfourR : 4 * ((L + 1 : ℕ) : ℝ) < N := by exact_mod_cast hfour
  push_cast at hfourR
  linarith only [hc, hirr, hfR, hfourR]

theorem uniform_mass_lower (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → c * (N : ℝ) ^ (-1 : ℝ) ≤ mass N L := by
  let c : ℝ := (((2 : ℝ) ^ C)⁻¹) ^ 2 / 2
  obtain ⟨NC, _hNC, hc⟩ := uniform_regular_union_count C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨c, by dsimp [c]; positivity, max 2 (max NC NG), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hnom := CriticalChannelPowers.nominal_square_lower (by omega : 2 ≤ N) hband
  have hpow : (2 ^ (2 * L) : ℝ)⁻¹ = ((2 ^ L : ℝ)⁻¹) ^ 2 := by rw [Nat.mul_comm 2 L, pow_mul, inv_pow]
  calc
    _ = ((N : ℝ) / 2) * (((2 : ℝ) ^ C)⁻¹) ^ 2 * (N : ℝ) ^ (-2 : ℝ) := by
      dsimp [c]
      rw [Real.rpow_neg_one, Real.rpow_neg hn.le, Real.rpow_two]
      field_simp
    _ ≤ ((N : ℝ) / 2) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hnom (by positivity : 0 ≤ (N : ℝ) / 2)
      simpa only [mul_assoc] using h
    _ ≤ ((regularUnionStarts N L).card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband) (sq_nonneg _)
    _ = ((regularUnionStarts N L).card : ℝ) * (2 ^ (2 * L) : ℝ)⁻¹ := by rw [hpow]
    _ ≤ _ := mass_lower (by omega) hL

theorem uniform_mass_upper (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NJ, _hNJ, hj⟩ := ContactSeedKernel.uniform_joint_mass C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NJ NG), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  exact (sum_le_sum_of_subset_of_nonneg (subset_close N L hL)
    (fun e _ _ ↦ infiniteJointMoment_nonneg L e)).trans (hj N (by omega) L hband (dyadicBlock N) (subset_refl _))

theorem uniform_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ (-1 - ε) ≤ ActiveEdgeObservables.probability (edges N L) L ∧
        ActiveEdgeObservables.probability (edges N L) L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨c, hc, NM, _hNM, hm⟩ := uniform_mass_lower C
  obtain ⟨NU, _hNU, hu⟩ := uniform_mass_upper C ε hε
  obtain ⟨NA, _hNA, ha⟩ := ActiveEdgeMoments.uniform_activation 2 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / c) (-1 - ε) (ε / 2) (by positivity)
  refine ⟨max 2 (max NM (max NU (max NA (max NG NF)))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hact := ha N (by omega) L hband (dyadicBlock N) (subset_refl _) (edges N L) (subset_pairs N L hL)
  have hlow : (N : ℝ) ^ (-1 - ε) ≤ c * (N : ℝ) ^ (-1 - ε / 2) := by
    have h := mul_le_mul_of_nonneg_left (hf N (by omega)) hc.le
    convert h using 1
    · field_simp
    · congr 2
      ring
  refine ⟨?_, hact.2.trans (hu N (by omega) L hband)⟩
  calc
    _ ≤ c * (N : ℝ) ^ (-1 - ε / 2) := hlow
    _ = (c * (N : ℝ) ^ (-1 : ℝ)) * (N : ℝ) ^ (-(ε / 2)) := by rw [mul_assoc, ← Real.rpow_add hn]; congr 2
    _ ≤ mass N L * (N : ℝ) ^ (-(ε / 2)) :=
      mul_le_mul_of_nonneg_right (hm N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ ≤ _ := hact.1

theorem uniform_close_probability (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ (-1 - ε) ≤ ActiveEdgeObservables.probability (ClosePairs.pairs (dyadicBlock N) L) L ∧
        ActiveEdgeObservables.probability (ClosePairs.pairs (dyadicBlock N) L) L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := uniform_probability C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NP NG), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  rw [ActualActiveFamilyCover.close_probability_eq_exact N L hL]
  exact hp N (by omega) L hband

end PaperP1.ExactContactActivation
