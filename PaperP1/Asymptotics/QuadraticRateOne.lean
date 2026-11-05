module

public import PaperP1.Asymptotics.TripleActivityLawReconstruction
public import PaperP1.Asymptotics.RegularQuadraticReferenceRestoration

/-! # Both first quadratic approximations improve from four fifths to rate one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticRateOne

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.TripleActivityLawReconstruction

theorem uniform_exact (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
          (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := TripleActivityLawReconstruction.uniform_estimates C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NF + NA, by omega, ?_⟩
  intro N hN L hband G hG
  obtain ⟨hA3, hdist⟩ := ha N (by omega) L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsmall : min ((ε / 4) / 16) (1 / 48) ≤ ε / 64 := by
    have hs : (ε / 4) / 16 = ε / 64 := by ring
    simpa only [hs] using (min_le_left (ε / 64) (1 / 48))
  have hfirst : (N : ℝ) ^ (ε / 4) * CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤
      (N : ℝ) ^ (-1 + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-1 + min ((ε / 4) / 16) (1 / 48)) :=
        mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = (N : ℝ) ^ (ε / 4 + (-1 + min ((ε / 4) / 16) (1 / 48))) := (Real.rpow_add hn _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hsmall, hε])
  have hsecond : (N : ℝ) ^ (-4 / 3 + ε / 4) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hdist, hfirst, hsecond, hfactor]

theorem companion_T17_5 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let μ := countMoment (dyadicBlock N) L 1
        let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
        let ν := (N : ℝ) * (2 ^ L : ℝ)⁻¹
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference μ α) ≤ (N : ℝ) ^ (-1 + ε) ∧
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference ν α) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_exact C (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := RegularQuadraticReferenceRestoration.uniform_reference_errors C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NT + NF + NR, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := RegularStarts.regularStarts N L
  let Q := QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)
  let P := (N : ℝ) ^ (-1 + ε / 2)
  let U := (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  let R := (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
  have hrest := ht N (by omega) L hband
  have hregular : SignedAtomicDistance.distance R Q ≤ P :=
    hr N (by omega) L hband G (RegularStarts.regularStarts_subset N L)
  have hfactor : 2 * P ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have htriangle (S : SignedMeasure ℕ) : SignedAtomicDistance.distance U S ≤
      SignedAtomicDistance.distance U R + SignedAtomicDistance.distance R Q + SignedAtomicDistance.distance Q S := by
    have hUR := SignedAtomicDistance.triangle U R S
    have hRQ := SignedAtomicDistance.triangle R Q S
    linarith only [hUR, hRQ]
  constructor
  · apply (htriangle _).trans
    apply le_trans _ hfactor
    linarith only [hregular, hrest.1]
  · apply (htriangle _).trans
    apply le_trans _ hfactor
    linarith only [hregular, hrest.2]

end PaperP1.QuadraticRateOne
