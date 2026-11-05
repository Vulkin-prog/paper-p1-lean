module

public import PaperP1.Asymptotics.SourcePairSignedCentering
public import PaperP1.Asymptotics.PairProfiles

/-! # The signed arithmetic source profile with its exact finite channel sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSourceProfile

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

def mainTerm (N L : ℕ) : ℝ := (N : ℝ) / 3 *
  ((ChannelSumIdentity.signed L 2 3 : ℤ) + (ChannelSumIdentity.signed L 3 4 : ℤ))

theorem scaled_mainTerm (N L : ℕ) :
    ((2 ^ L : ℝ)⁻¹) ^ 2 * mainTerm N L =
      ChannelMainTermBounds.mainTerm N L 2 3 + ChannelMainTermBounds.mainTerm N L 3 4 := by
  norm_num [mainTerm, ChannelMainTermBounds.mainTerm, ActualSourceTranslations.coefficient]; ring

theorem unscale {N L : ℕ} {C θ x y : ℝ} (hN : 2 ≤ N)
    (hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (hscaled : |((2 ^ L : ℝ)⁻¹) ^ 2 * x - ((2 ^ L : ℝ)⁻¹) ^ 2 * y| ≤ (N : ℝ) ^ θ) :
    |x - y| ≤ ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (2 + θ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : ((2 ^ L : ℝ)⁻¹) ^ 2 * |x - y| ≤ (N : ℝ) ^ θ := by
    rwa [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)] at hscaled
  have heq : (2 ^ L : ℝ) ^ 2 * (((2 ^ L : ℝ)⁻¹) ^ 2 * |x - y|) = |x - y| := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hprod (sq_nonneg (2 ^ L : ℝ))
  rw [heq] at hmul
  have hword := CriticalChannelPowers.word_upper hN hcrit
  calc
    _ ≤ (2 ^ L : ℝ) ^ 2 * (N : ℝ) ^ θ := hmul
    _ ≤ ((2 : ℝ) ^ C * N) ^ 2 * (N : ℝ) ^ θ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hword 2) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [Real.rpow_add hNpos, Real.rpow_two]; ring

theorem uniform_all_ordered (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |(∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), SourcePairAffineWeight.signedWeight p.1 p.2 L) -
          mainTerm N L| ≤ (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨Np, _hNp, hp⟩ :=
    PairProfiles.uniform_profiles C (ε / 4) 8 (by positivity)
  obtain ⟨Ne, _hNe, he⟩ := SourcePairSignedCentering.uniform_error C (ε / 4) (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 4) (ε / 4) (by positivity)
  obtain ⟨Nu, hu⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2)
    (6 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Np (max Ne (max Nf Nu))), by omega, ?_⟩
  intro N hN L hcrit
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have herr := he N (by omega) L hcrit
  have hmain := (hp N (by omega) L (8 * (L + 1)) hcrit le_rfl le_rfl).2
  rw [← scaled_mainTerm] at hmain
  have hcompare : (N : ℝ) ^ (-1 + ε / 4) ≤ (N : ℝ) ^ (-4 / 5 + ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hscaled : |((2 ^ L : ℝ)⁻¹) ^ 2 *
      (∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), SourcePairAffineWeight.signedWeight p.1 p.2 L) -
      ((2 ^ L : ℝ)⁻¹) ^ 2 * mainTerm N L| ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    have htriangle := abs_sub_le (((2 ^ L : ℝ)⁻¹) ^ 2 *
      (∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), SourcePairAffineWeight.signedWeight p.1 p.2 L))
      (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)
      (((2 ^ L : ℝ)⁻¹) ^ 2 * mainTerm N L)
    have htwo : 2 * (N : ℝ) ^ (-4 / 5 + ε / 4) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := by
      convert hf N (by omega) using 1
      congr 1
      ring
    linarith only [htriangle, herr, hmain, hcompare, htwo]
  have hraw := unscale (by omega : 2 ≤ N) hcrit hscaled
  have hexp : (2 : ℝ) + (-4 / 5 + ε / 2) = 6 / 5 + ε / 2 := by ring
  rw [hexp] at hraw
  exact hraw.trans (by convert hu N (by omega) using 1; congr 1; ring)

end PaperP1.SignedSourceProfile
