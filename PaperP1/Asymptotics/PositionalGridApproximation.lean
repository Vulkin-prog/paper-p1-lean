module

public import PaperP1.Asymptotics.PositionalWeightedApproximation
public import PaperP1.Probability.PositionalGrid

/-! # Main 20.1 on the literal original finite grid, at every fixed weight

The target is a probability measure whose singleton masses are the exact
single/pair convolution coefficients, with the original arithmetic edge rates.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalGridApproximation

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.RetainedComponentActivity

theorem main_20_1 (C ε : ℝ) (hε : 0 < ε) :
    ∀ j : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let G := dyadicBlock N
        let T := PositionalCompoundPoisson.target G
          (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        ∃ Q : ProbabilityMeasure (G → ℕ),
          (∀ z : G → ℕ, (Q : Measure (G → ℕ)).real {z} = coeff (PositionalGrid.encode G z) T) ∧
          (∑' z : G → ℕ, (1 + ∑ x : G, (z x : ℝ)) ^ j *
            |infiniteRademacherMeasure.real
                {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} -
              (Q : Measure (G → ℕ)).real {z}|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  have hp := PositionalWeightedApproximation.uniform_coefficient_bound C ε hε
  obtain ⟨NP, _hNP, hprob⟩ := WeakPairIncidence.full_target_isProbability C
  intro j
  obtain ⟨NN, _hNN, hh⟩ := hp j
  refine ⟨10 + NP + NN, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := dyadicBlock N
  let T := PositionalCompoundPoisson.target G
    (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  let A := ofFinite (PositionalStoppedLaw.actualLaw G L)
  have hPT : PositivePositionalConvolution.IsProbability T :=
    hprob N (by omega) L hband (8 * (L + 1) : ℕ)
  have hST : PositionalGroundSupport.Supported G T :=
    PositionalGroundSupport.supported_target G _ _ _ (fun e he ↦
      (RetainedGoodEdges.good_pair_regular (by omega) e he).trans
        (RegularStarts.regularStarts_subset N L))
  have hSA : PositionalGroundSupport.Supported G A :=
    PositionalGroundSupport.supported_law G _ _
  let Q := PositionalGrid.law G T hPT hST
  refine ⟨Q, fun z ↦ PositionalGrid.real_singleton G T hPT hST z, ?_⟩
  have hevent (z : G → ℕ) :
      {ω | configuration G (fun x ↦ infiniteStartIndicator x L) ω = PositionalGrid.encode G z} =
        {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} := by
    ext ω
    exact PositionalGrid.configuration_eq_encode G _ ω z
  calc
    _ = ∑' z : G → ℕ, (1 + ∑ x : G, (z x : ℝ)) ^ j *
        |coeff (PositionalGrid.encode G z) A - coeff (PositionalGrid.encode G z) T| := by
      apply tsum_congr
      intro z
      rw [show (Q : Measure (G → ℕ)).real {z} = coeff (PositionalGrid.encode G z) T from
        PositionalGrid.real_singleton G T hPT hST z]
      rw [show coeff (PositionalGrid.encode G z) A =
        infiniteRademacherMeasure.real
          {ω | ∀ x : G, (infiniteStartIndicator x.val L ω).toNat = z x} by
        rw [show A = ofFinite (PositionalStoppedLaw.actualLaw G L) from rfl,
          coeff_ofFinite, PositionalStoppedLaw.actualLaw_coeff, hevent]]
    _ = ∑' v : Configuration ℕ, (1 + (PositionalCountProjection.totalCount v : ℝ)) ^ j *
        |coeff v A - coeff v T| := PositionalGrid.weighted_difference_eq G A T hSA hST j
    _ ≤ _ := by
      simpa only [A, G, T, coeff_ofFinite] using (hh N (by omega) L hband).2

end PaperP1.PositionalGridApproximation
