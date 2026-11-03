module

public import PaperP1.Model.SourcePairSignedSum
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Unconditional nominal-centering error in the actual arithmetic pair sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairSignedCentering

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.SourcePairAffineWeight

theorem nominal_diagonal {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (N : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnom := LocalRigidityConsequences.nominal_marginal_bound hN hcrit
  calc
    _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnom 2) hNpos.le
    _ = _ := by rw [Real.rpow_neg_one]; field_simp

theorem uniform_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |((2 ^ L : ℝ)⁻¹) ^ 2 *
        (∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), signedWeight p.1 p.2 L) -
          RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L| ≤
        (N : ℝ) ^ (-1 + ε) := by
  let R := (2 : ℝ) ^ C
  obtain ⟨Nb, _hNb, hb⟩ := CriticalActualMean.uniform_nominal_bias C (ε / 2) (by positivity)
  obtain ⟨Nm, _hNm, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (4 * R ^ 2) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nb (max Nm (max Ng Na))), by omega, ?_⟩
  intro N hN L hcrit
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hcrit).2.2.1; omega
  have hcore := SourcePairSignedSum.centering_error (G := dyadicBlock N) (subset_refl _) hL
  rw [dyadicBlock_card] at hcore
  have hmu := (hm N (by omega) L hcrit).2
  have hnom := LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hcrit
  have hlam : (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ R := by
    have h := (le_div_iff₀ hNpos).mp hnom
    dsimp [R]
    nlinarith only [h]
  have hsum : countMoment (dyadicBlock N) L 1 + (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ 3 * R := by
    dsimp [R] at *
    linarith only [hmu, hlam]
  have hbias := hb N (by omega) L hcrit
  have hproduct := mul_le_mul hsum hbias (abs_nonneg _) (by dsimp [R]; positivity : (0 : ℝ) ≤ 3 * R)
  have hdiag := nominal_diagonal (by omega : 2 ≤ N) hcrit
  have hcompare : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hdiag' : (N : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ R ^ 2 * (N : ℝ) ^ (-1 + ε / 2) :=
    hdiag.trans (mul_le_mul_of_nonneg_left hcompare (sq_nonneg R))
  have htotal : |((2 ^ L : ℝ)⁻¹) ^ 2 *
      (∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), signedWeight p.1 p.2 L) -
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L| ≤
      (4 * R ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by
    dsimp [R] at hproduct hdiag' ⊢
    nlinarith only [hcore, hproduct, hdiag']
  exact htotal.trans (by convert ha N (by omega) using 1; congr 1; ring)

end PaperP1.SourcePairSignedCentering
