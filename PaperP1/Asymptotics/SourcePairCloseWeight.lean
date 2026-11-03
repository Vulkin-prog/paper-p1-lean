module

public import PaperP1.Combinatorics.PairSeparation
public import PaperP1.Asymptotics.ContactSeedKernel
public import PaperP1.Asymptotics.SignedSourceProfileUnderInputs

/-! # The actual close-pair signed arithmetic weight has an unconditional near-linear total -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairCloseWeight

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.SourcePairAffineWeight
  PaperP1.PairSeparation

theorem nominal_mass (G : Finset ℕ) (L : ℕ) :
    (∑ _e ∈ ClosePairs.pairs G L, ((2 ^ L : ℝ)⁻¹) ^ 2) ≤
      (L : ℝ) * G.card * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  have h := ClosePairs.independent_weight_bound G L (fun _ ↦ (2 ^ L : ℝ)⁻¹)
    (fun _ ↦ by positivity) ((2 ^ L : ℝ)⁻¹) (by positivity) (fun _ _ ↦ le_rfl)
  have heq : (∑ e ∈ ClosePairs.pairs G L, ∏ _x ∈ e, (2 ^ L : ℝ)⁻¹) =
      ∑ _e ∈ ClosePairs.pairs G L, ((2 ^ L : ℝ)⁻¹) ^ 2 := by
    apply sum_congr rfl
    intro e he
    have hc := (mem_powersetCard.mp (ClosePairs.subset G L he)).2
    simp only [prod_const, hc]
  rw [heq] at h
  simp only [sum_const, nsmul_eq_mul] at h ⊢
  nlinarith only [h]

theorem finite_scaled_abs (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    ((2 ^ L : ℝ)⁻¹) ^ 2 * (∑ p ∈ closeHosts G L, |signedWeight p.1 p.2 L|) ≤
      2 * ((∑ e ∈ ClosePairs.pairs G L, infiniteJointMoment L e) +
        ∑ _e ∈ ClosePairs.pairs G L, ((2 ^ L : ℝ)⁻¹) ^ 2) := by
  calc
    _ = ∑ p ∈ closeHosts G L,
        |infiniteJointMoment L {p.1, p.2} - ((2 ^ L : ℝ)⁻¹) ^ 2| := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _hp
      rw [← scaled_signed_weight p.1 p.2 L hL, abs_mul, abs_of_nonneg (sq_nonneg ((2 ^ L : ℝ)⁻¹))]
    _ = 2 * ∑ e ∈ ClosePairs.pairs G L, |infiniteJointMoment L e - ((2 ^ L : ℝ)⁻¹) ^ 2| :=
      PairSubfamilyWeights.weighted_sum G (ClosePairs.pairs G L) (ClosePairs.subset G L)
        (fun e ↦ |infiniteJointMoment L e - ((2 ^ L : ℝ)⁻¹) ^ 2|)
    _ ≤ 2 * ∑ e ∈ ClosePairs.pairs G L, (infiniteJointMoment L e + ((2 ^ L : ℝ)⁻¹) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro e _he
      have h := abs_sub (infiniteJointMoment L e) (((2 ^ L : ℝ)⁻¹) ^ 2)
      simpa only [abs_of_nonneg (infiniteJointMoment_nonneg L e), abs_of_nonneg (sq_nonneg ((2 ^ L : ℝ)⁻¹))] using h
    _ = _ := by rw [sum_add_distrib]

theorem uniform_nominal_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ _e ∈ ClosePairs.pairs (dyadicBlock N) L, ((2 ^ L : ℝ)⁻¹) ^ 2) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nl, hl⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow CriticalBandScale.upperScale 1 (ε / 2) (by positivity)
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Ns (max Nl Na)), by omega, ?_⟩
  intro N hN L hcrit
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpow : (L : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hle : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    exact hle.trans ((hs N (by omega) L hcrit).2.trans
      (by simpa only [Real.rpow_one] using hl N (by omega)))
  have hdiag := SourcePairSignedCentering.nominal_diagonal (by omega : 2 ≤ N) hcrit
  have hfinite := nominal_mass (dyadicBlock N) L
  rw [dyadicBlock_card] at hfinite
  calc
    _ ≤ (L : ℝ) * N * ((2 ^ L : ℝ)⁻¹) ^ 2 := hfinite
    _ = (L : ℝ) * ((N : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2) := by ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 : ℝ)) :=
      mul_le_mul hLpow hdiag (by positivity) (Real.rpow_nonneg hNpos.le _)
    _ = ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [mul_left_comm, ← Real.rpow_add hNpos]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_scaled_abs (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (∑ p ∈ closeHosts (dyadicBlock N) L, |signedWeight p.1 p.2 L|) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Nj, _hNj, hj⟩ := ContactSeedKernel.uniform_joint_mass C (ε / 2) (by positivity)
  obtain ⟨Nn, _hNn, hn⟩ := uniform_nominal_mass C (ε / 2) (by positivity)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption 4 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nj (max Nn (max Ng Na))), by omega, ?_⟩
  intro N hN L hcrit
  have hL : 0 < L := by have h := (hg N (by omega) L hcrit).2.2.1; omega
  have hfinite := finite_scaled_abs (dyadicBlock N) L hL
  have hq := hj N (by omega) L hcrit (dyadicBlock N) (subset_refl _)
  have hp := hn N (by omega) L hcrit
  have hfour : 4 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  linarith only [hfinite, hq, hp, hfour]

theorem uniform_abs (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ p ∈ closeHosts (dyadicBlock N) L, |signedWeight p.1 p.2 L|) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨Ns, _hNs, hs⟩ := uniform_scaled_abs C (ε / 2) (by positivity)
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2)
    (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Ns Na), by omega, ?_⟩
  intro N hN L hcrit
  have hsum : 0 ≤ ∑ p ∈ closeHosts (dyadicBlock N) L, |signedWeight p.1 p.2 L| :=
    sum_nonneg fun _ _ ↦ abs_nonneg _
  have hscaled : |((2 ^ L : ℝ)⁻¹) ^ 2 *
      (∑ p ∈ closeHosts (dyadicBlock N) L, |signedWeight p.1 p.2 L|) - ((2 ^ L : ℝ)⁻¹) ^ 2 * 0| ≤
        (N : ℝ) ^ (-1 + ε / 2) := by
    simpa only [mul_zero, sub_zero, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsum)] using hs N (by omega) L hcrit
  have hraw := SignedSourceProfileUnderInputs.unscale (by omega : 2 ≤ N) hcrit hscaled
  rw [sub_zero, abs_of_nonneg hsum, show (2 : ℝ) + (-1 + ε / 2) = 1 + ε / 2 by ring] at hraw
  exact hraw.trans (by convert ha N (by omega) using 1; congr 1; ring)

end PaperP1.SourcePairCloseWeight
