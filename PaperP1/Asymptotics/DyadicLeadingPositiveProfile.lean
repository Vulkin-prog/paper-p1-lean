module

public import PaperP1.Asymptotics.DyadicLeadingPairGeometry
public import PaperP1.Asymptotics.DyadicFixedChannelComparison
public import PaperP1.Asymptotics.MacroscopicActualLeadingProfiles

/-! # The actual full dyadic leading positive channel

The literal2:3/3:2 mask has main term N/3 times the exact finite unsigned
channel sum, retaining nonprivate and zero-unit geometric pairs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicLeadingPositiveProfile

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedPairRankLoss PaperP1.NormalizedUnitCount
  PaperP1.DyadicAlignedPairMasks PaperP1.DyadicLeadingPairGeometry PaperP1.UnsignedUnitFourierAggregate
  PaperP1.CriticalBandScale

def rationalTotal (N L : ℕ) : ℝ := 2 * ∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight 2 3 x y L

def positive (N L : ℕ) : ℝ := ∑ xy ∈ leading N L, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1)

theorem uniform_comparison (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → |positive N L - rationalTotal N L| ≤ (N : ℝ) ^ (5 / 6 + ε) := by
  obtain ⟨MS, hS⟩ := uniform_symmetric_sum C
  obtain ⟨MC, hC⟩ := PaperP1.DyadicFixedChannelComparison.height_three C (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (5 / 6 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MS (max MC MF), ?_⟩
  intro N hN L hcrit
  let E := channel N L 2 3
  have hp := hC N (by omega) L hcrit E (Subset.refl _)
  have hr : rationalTotal N L = 2 * ∑ xy ∈ E, unitWeight 2 3 xy.1 xy.2 L := by
    unfold rationalTotal
    rw [rational_forward_sum (by omega : 2 ≤ N)]
  have hs : positive N L = 2 * ∑ xy ∈ E, ((2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1) := by
    apply (hS N (by omega) L hcrit).2.2
    intro xy
    change (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 = (2 ^ pairLoss xy.2 xy.1 L : ℝ) - 1
    rw [pairLoss_comm xy.1 xy.2 L]
  rw [hs, hr]
  have hh := PaperP1.MacroscopicActualLeadingProfiles.doubled_sum_error E
    (fun xy ↦ (2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1) (fun xy ↦ unitWeight 2 3 xy.1 xy.2 L)
  have heq : (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 1 - unitWeight 2 3 xy.1 xy.2 L|) =
      ∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units 2 3 xy.1 xy.2 L).card - 1)| := by
    apply sum_congr rfl
    intro xy _
    unfold unitWeight
    congr 1
    ring
  rw [heq] at hh
  have hf : 2 * (N : ℝ) ^ (5 / 6 + ε / 2) ≤ (N : ℝ) ^ (5 / 6 + ε) := by
    simpa only [show (5 : ℝ) / 6 + ε / 2 + ε / 2 = 5 / 6 + ε by ring] using hF N (by omega)
  exact hh.trans ((mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)).trans hf)

theorem finite_error {N L : ℕ} (hN : 2 ≤ N) (hlarge : 5 * (L + 1) < N) :
    |rationalTotal N L - (N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ)| ≤
      6 * ((L + 1 : ℕ) : ℝ) * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ) := by
  have hh := PaperP1.UnsignedUnitFourierAggregate.finite_unsigned_sum_error hN (by omega : 0 < 2)
    (by omega : 2 < 3) (by omega : 3 < 2 * 2) (by norm_num : Nat.Coprime 2 3) (by simpa using hlarge)
  rw [PaperP1.ActualSourceTranslations.leading_coefficients.1] at hh
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
  simpa only [rationalTotal, div_eq_mul_inv, one_mul] using hh

theorem endpoint_rate (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      6 * ((L + 1 : ℕ) : ℝ) * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ) ≤ (N : ℝ) ^ (1 / 3 + ε) := by
  let K : ℝ := (2 : ℝ) ^ ((C + 1) / 3)
  obtain ⟨MB, hB⟩ := critical_band_scale C
  obtain ⟨MP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (6 * K) 3 ε hε
  refine ⟨max MB MP, ?_⟩
  intro N hN L hcrit
  have hn2 : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 3) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ) := by
    simpa only [Nat.cast_ofNat] using PaperP1.CriticalChannelPowers.window_root_upper hn2 (by omega : 0 < 3) hcrit
  have hpoly : 6 * K * ((L + 1 : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) ^ ε := by
    have hp := hP N (by omega) L (hB N (by omega) L hcrit).2
    rw [abs_of_nonneg (by dsimp [K]; positivity : (0 : ℝ) ≤ 6 * K * (L + 1 : ℝ) ^ 3)] at hp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  have hupper := PaperP1.ChannelUnsignedBound.unsigned_upper_rpow (L := L) (by omega : 0 < 3) (by omega : 2 ≤ 3)
  norm_num only [Nat.cast_ofNat] at hupper
  calc
    _ ≤ 6 * ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ ≤ 6 * ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2 * (K * (N : ℝ) ^ (1 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot (sq_nonneg _)) (by positivity)
    _ = (6 * K * ((L + 1 : ℕ) : ℝ) ^ 3) * (N : ℝ) ^ (1 / 3 : ℝ) := by ring
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_main_term (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |positive N L - (N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ)| ≤ (N : ℝ) ^ (5 / 6 + ε) := by
  obtain ⟨MC, hC⟩ := uniform_comparison C (ε / 2) (by positivity)
  obtain ⟨ME, hE⟩ := endpoint_rate C (ε / 2) (by positivity)
  obtain ⟨ML, hL⟩ := PaperP1.CriticalPolynomialScale.polynomial_lt_scale C 5 (by norm_num) 1
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (5 / 6 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MC (max ME (max ML MF)), ?_⟩
  intro N hN L hcrit
  have hc := hC N (by omega) L hcrit
  have he := hE N (by omega) L hcrit
  have hl := hL N (by omega) L hcrit
  simp only [pow_one] at hl
  have hlarge : 5 * (L + 1) < N := by exact_mod_cast hl
  have hfinite := finite_error (by omega : 2 ≤ N) hlarge
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (1 / 3 + ε / 2) ≤ (N : ℝ) ^ (5 / 6 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hf : 2 * (N : ℝ) ^ (5 / 6 + ε / 2) ≤ (N : ℝ) ^ (5 / 6 + ε) := by
    simpa only [show (5 : ℝ) / 6 + ε / 2 + ε / 2 = 5 / 6 + ε by ring] using hF N (by omega)
  exact (abs_sub_le (positive N L) (rationalTotal N L)
    ((N : ℝ) / 3 * (PaperP1.ChannelSumIdentity.unsigned L 2 3 : ℤ))).trans
      ((by linarith only [hc, hfinite.trans (he.trans hpower)] : _ ≤ 2 * (N : ℝ) ^ (5 / 6 + ε / 2)).trans hf)

end PaperP1.DyadicLeadingPositiveProfile
