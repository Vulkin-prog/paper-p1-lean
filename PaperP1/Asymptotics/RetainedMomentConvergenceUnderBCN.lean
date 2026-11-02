module

public import PaperP1.Model.RetainedMomentTransfer
public import PaperP1.Asymptotics.FixedCountMomentBoundsUnderBCN
public import PaperP1.Asymptotics.RetainedBadProbabilityUnderBCN
public import PaperP1.Asymptotics.CoarsePoissonLawUnderBCN

/-! # Actual retained count moments and probability laws converge with the original count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedMomentConvergenceUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.RetainedCountCylinder PaperP1.RetainedMomentTransfer

theorem uniform_moment_transfer (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ H : ℝ,
      |countMoment G L j - modifiedMoment H N L G j| ≤ ε := by
  obtain ⟨B, hB, NM, _hNM, hmom⟩ := FixedCountMomentBoundsUnderBCN.uniform_ordinary_bound (j + 1) c κ hc hBCN C
  let R : ℝ := 1 + 2 * B / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have htail : B / R ≤ ε / 2 := by
    apply (div_le_iff₀ hR).mpr
    have hid : (ε / 2) * R = B + ε / 2 := by dsimp [R]; field_simp; ring
    rw [hid]
    linarith only [hε]
  have htol : 0 < ε / (2 * R ^ j) := by positivity
  obtain ⟨NB, _hNB, hbad⟩ := RetainedBadProbabilityUnderBCN.uniform_badProbability c κ hc hBCN C _ htol
  refine ⟨max 2 (max NM NB), by omega, ?_⟩
  intro N hN L hband G hG H
  have hfirst : R ^ j * badProbability H N L G ≤ ε / 2 := by
    calc
      _ ≤ R ^ j * (ε / (2 * R ^ j)) :=
        mul_le_mul_of_nonneg_left (hbad N (by omega) L hband G hG H) (pow_nonneg hR.le j)
      _ = _ := by field_simp
  have hsecond : countMoment G L (j + 1) / R ^ (j + 1 - j) ≤ ε / 2 := by
    rw [show j + 1 - j = 1 by omega, pow_one]
    exact (div_le_div_of_nonneg_right (hmom N (by omega) L hband G hG) hR.le).trans htail
  have h := moment_truncation H N L G j (j + 1) (by omega) R hR
  linarith only [h, hfirst, hsecond]

theorem uniform_poisson_totalVariation (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      AtomicProbability.totalVariation (RetainedModifiedLaw.law H N L (dyadicBlock N))
        (CoarsePoissonLawUnderBCN.actualPoissonLaw N L) ≤ ε ∧
      AtomicProbability.totalVariation (RetainedModifiedLaw.law H N L (dyadicBlock N))
        (CoarsePoissonLawUnderBCN.nominalPoissonLaw N L) ≤ ε := by
  obtain ⟨NA, _hNA, hactual⟩ := CoarsePoissonLawUnderBCN.uniform_totalVariation c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NN, _hNN, hnominal⟩ := CoarsePoissonLawUnderBCN.uniform_nominal_totalVariation c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hbad⟩ := RetainedBadProbabilityUnderBCN.uniform_badProbability c κ hc hBCN C (ε / 2) (by positivity)
  refine ⟨max 2 (max NA (max NN NB)), by omega, ?_⟩
  intro N hN L hband H
  have hcoup := RetainedModifiedLaw.coupling H N L (dyadicBlock N)
  rw [AtomicProbability.totalVariation_symm] at hcoup
  have hb := hbad N (by omega) L hband (dyadicBlock N) (subset_refl _) H
  have ha := hactual N (by omega) L hband
  have hn := hnominal N (by omega) L hband
  have hta := AtomicProbabilityMetric.triangle (RetainedModifiedLaw.law H N L (dyadicBlock N))
    (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) (CoarsePoissonLawUnderBCN.actualPoissonLaw N L)
  have htn := AtomicProbabilityMetric.triangle (RetainedModifiedLaw.law H N L (dyadicBlock N))
    (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) (CoarsePoissonLawUnderBCN.nominalPoissonLaw N L)
  constructor <;> linarith only [hcoup, hb, ha, hn, hta, htn]

end PaperP1.RetainedMomentConvergenceUnderBCN
