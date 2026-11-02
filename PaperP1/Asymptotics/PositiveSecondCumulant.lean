module

public import PaperP1.Model.PrivateChannelHostSupport
public import PaperP1.Asymptotics.PrivateChannelMassPhase
public import PaperP1.Asymptotics.SecondCumulantUnderBCN
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Unconditional positivity of the actual second factorial cumulant

Only the positive 2:3 channel, the unweighted host count and the marginal
diagonal are needed for the lower bound. The full pair profile and BCN
are not premises. The final two-sided Hermite admissibility adds BCN
solely for the previously proved upper bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveSecondCumulant

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.PrivateChannelHostSupport PaperP1.PrivateChannelSources
  PaperP1.HeterogeneousBernoulli

theorem uniform_lower (C : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      d * L * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L := by
  obtain ⟨d, k, hd, _hk, NP, hphase⟩ := PrivateChannelMassPhase.positive_phase C 6 2 3
    (by norm_num) (by norm_num) (by norm_num) (by decide)
  obtain ⟨NI, hind⟩ := PairHostIndependentMass.uniform_mass C (1 / 6) (by norm_num)
  obtain ⟨K, _hK, NM, hmarg⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NS, hscale⟩ := CriticalPolynomialScale.polynomial_lt_scale C 5 (by norm_num) 1
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption
    (2 * (1 + K ^ 2) / d) (-5 / 6) (1 / 6) (by norm_num)
  refine ⟨d / 2, by positivity, max 2 (max NP (max NI (max NM (max NS (max NG NF))))), by omega, ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hlarge : (2 + 3) * (L + 1) < N := by
    have h := hscale N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  have hfinite := channel_cumulant_lower (H := 6 * (L + 1)) hNtwo (by norm_num : 0 < (2 : ℕ))
    (by norm_num : (2 : ℕ) < 3) hlarge hL
  have hp := (hphase N (by omega) L (6 * (L + 1)) hband (by omega) le_rfl).1
  norm_num only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 3 = -2 / 3 by ring] at hp
  have hi := hind N (by omega) L hband
  norm_num only [show -(1 : ℝ) + 1 / 6 = -5 / 6 by ring] at hi
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) (subset_refl (dyadicBlock N))
    (fun x hx ↦ (hmarg N (by omega) L x hband hx).2)
  have hdg : powerSum (dyadicBlock N) (fun x ↦ infiniteMarginal x L) 2 ≤
      K ^ 2 * (N : ℝ) ^ (-5 / 6 : ℝ) := by
    calc
      _ ≤ K ^ 2 / N := hdiag
      _ = K ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (sq_nonneg K)
  have hf := hfactor N (by omega)
  norm_num only [show (-5 / 6 : ℝ) + 1 / 6 = -2 / 3 by ring] at hf
  have hratio : (d / 2) * (2 * (1 + K ^ 2) / d) = 1 + K ^ 2 := by
    calc
      _ = (d / d) * (1 + K ^ 2) := by ring
      _ = _ := by rw [div_self hd.ne', one_mul]
  have herror : PairHostIndependentMass.mass N L +
      powerSum (dyadicBlock N) (fun x ↦ infiniteMarginal x L) 2 ≤
        (d / 2) * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    calc
      _ ≤ (1 + K ^ 2) * (N : ℝ) ^ (-5 / 6 : ℝ) := by nlinarith only [hi, hdg]
      _ = (d / 2) * ((2 * (1 + K ^ 2) / d) * (N : ℝ) ^ (-5 / 6 : ℝ)) := by
        rw [← mul_assoc, hratio]
      _ ≤ (d / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
        simpa only [neg_div] using mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ d / 2)
      _ ≤ _ := by
        have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
        have hpos : 0 ≤ (d / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := by positivity
        nlinarith only [mul_le_mul_of_nonneg_left hL1 hpos]
  nlinarith only [hfinite, hp, herror]

theorem uniform_positive (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L := by
  obtain ⟨d, hd, NA, hNA, hlower⟩ := uniform_lower C
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NA NG, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (mul_pos (mul_pos hd (by exact_mod_cast hL)) (Real.rpow_pos_of_pos hn _)).trans_le
    (hlower N (by omega) L hband)

theorem uniform_hermite_admissibility (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ∧
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L <
          countMoment (dyadicBlock N) L 1 := by
  obtain ⟨NP, hNP, hpositive⟩ := uniform_positive C
  obtain ⟨NG, hNG, hgap⟩ := SecondCumulantUnderBCN.uniform_parameter_gap c κ hc hBCN C
  exact ⟨max NP NG, by omega, fun N hN L hband ↦
    ⟨hpositive N (by omega) L hband, (hgap N (by omega) L hband).2⟩⟩

end PaperP1.PositiveSecondCumulant
