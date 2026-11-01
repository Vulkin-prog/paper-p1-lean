module

public import PaperP1.Model.SplitSumLp

/-! # Actual finite-cylinder moments equal the unrestricted split-sum Lp norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSplitLp

open scoped ENNReal
open Finset MeasureTheory PaperP1.Model PaperP1.Algebra PaperP1.SplitOffsetProducts
open PaperP1.ShortSplitMoments PaperP1.SplitSumLp PaperP1.Model.InfiniteRademacher
open PaperP1.Probability.CylinderExpectations PaperP1.Probability.InfiniteCylinderTransfer

local instance : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

def finiteSum (M : ℕ) (A : Finset ℤ) (S : Finset ℕ) (σ : SampleSpace M) : ℝ :=
  ∑ n ∈ S, (randomMultiplicativeValue σ (product A n) : ℝ)

theorem finiteSum_restrict (M : ℕ) (A : Finset ℤ) (S : Finset ℕ)
    (hcut : ∀ n ∈ S, product A n ≤ M) (ω : InfiniteSample) :
    finiteSum M A S (restrictToFinite M ω) = sumValue A S ω := by
  apply sum_congr rfl
  intro n hn
  rw [randomMultiplicativeValue_restrictToFinite_eq_infiniteRandomValue ω (hcut n hn)]

theorem moment_root_eq_lpNorm (M : ℕ) (A : Finset ℤ) (S : Finset ℕ)
    (hcut : ∀ n ∈ S, product A n ≤ M) (v : ℕ) (hv : 0 < v) :
    (finiteExpectation (cylinderProbability M).weight
      (fun σ ↦ |finiteSum M A S σ| ^ (v : ℝ))) ^ (1 / (v : ℝ)) =
      lpNorm (sumValue A S) (v : ℝ≥0∞) infiniteRademacherMeasure := by
  rw [lpNorm_eq_moment A S v hv]
  have hobs : (fun ω ↦ |sumValue A S ω| ^ v) =
      (fun ω ↦ |finiteSum M A S (restrictToFinite M ω)| ^ v) := by
    funext ω
    rw [finiteSum_restrict M A S hcut ω]
  rw [hobs, infiniteCylinder_integral M (fun σ ↦ |finiteSum M A S σ| ^ v)]
  simp only [Real.rpow_natCast]

end PaperP1.FiniteSplitLp
