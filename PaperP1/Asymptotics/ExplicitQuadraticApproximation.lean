module

public import PaperP1.Asymptotics.QuadraticRateOne
public import PaperP1.Asymptotics.ActualPairPhase
public import PaperP1.Asymptotics.ExplicitReferenceAdmissibility
public import PaperP1.Probability.PoissonParameterStability

/-! # The complete explicit two-channel probability reference of main Corollary 1.4 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitQuadraticApproximation

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteChannelHierarchy

theorem uniform_coefficient (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - twoChannelCoefficient N L| ≤
        (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨N₀, hN₀, hh⟩ := PairProfiles.uniform_profiles C ε 8 hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have h := (hh N hN L (8 * (L + 1)) hband le_rfl le_rfl).2
  have heq : ChannelMainTermBounds.mainTerm N L 2 3 + ChannelMainTermBounds.mainTerm N L 3 4 =
      twoChannelCoefficient N L := by
    rw [ActualPairPhase.main_sum N L (by omega)]
    unfold twoChannelCoefficient
    rfl
  rwa [heq] at h

theorem article_1_4 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L)) ≤
          (N : ℝ) ^ (-4 / 5 + ε) ∧
      AtomicSignedLaw.IsProbability (QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L)) ∧
      ∀ k : ℕ, QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L) {k} =
        Real.exp (-(nominalMean N L)) * (nominalMean N L) ^ k / (k.factorial : ℝ) *
          (1 + twoChannelCoefficient N L / 2 *
            (((k : ℝ) * ((k : ℝ) - 1)) / (nominalMean N L) ^ 2 -
              2 * (k : ℝ) / nominalMean N L + 1)) := by
  obtain ⟨NL, _hNL, hl⟩ := QuadraticRateOne.companion_T17_5 C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := uniform_coefficient C (ε / 2) (by positivity)
  obtain ⟨NQ, _hNQ, hq⟩ := ExplicitReferenceAdmissibility.uniform_two_channel_probabilities C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NL (max NP (max NQ NF))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let P := (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  let Q := QuadraticPoisson.reference (nominalMean N L) α
  let S := QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L)
  have hmean : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hdist : SignedAtomicDistance.distance P Q ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    ((hl N (by omega) L hband).2).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hcoef := hp N (by omega) L hband
  have hchange : SignedAtomicDistance.distance Q S ≤ 2 * |α - twoChannelCoefficient N L| := by
    have h := PoissonParameterStability.actual_signed_difference hmean hmean α (twoChannelCoefficient N L)
    simpa only [SignedAtomicDistance.distance, _root_.sub_apply, sub_self, abs_zero, mul_zero, zero_add] using h
  have htriangle := SignedAtomicDistance.triangle P Q S
  have hbound : SignedAtomicDistance.distance P S ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    calc
      _ ≤ 3 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [htriangle, hdist, hchange, hcoef]
      _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring
  exact ⟨hbound, (hq N (by omega) L hband).2.2.1,
    ExplicitReferenceAdmissibility.two_channel_mass_formula N L (by omega)⟩

end PaperP1.ExplicitQuadraticApproximation
