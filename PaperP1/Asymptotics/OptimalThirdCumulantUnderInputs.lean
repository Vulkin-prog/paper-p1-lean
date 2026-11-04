module

public import PaperP1.Asymptotics.SharpThirdActivityUnderInputs
public import PaperP1.Asymptotics.SharpThirdCumulantLowerUnderInputs

/-! # Both optimal41/30 bounds for the full original third factorial cumulant

The positive lower constant depends only on the fixed critical band.
All existing BCN and finite geometric properties remain explicit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalThirdCumulantUnderInputs

open Finset PaperP1.Model PaperP1.ThirdRunFactorialCumulant

def lowerConstant (C : ℝ) : ℝ := 5 * ThreeSlopePositiveActivity.lowerConstant C

theorem lowerConstant_pos (C : ℝ) : 0 < lowerConstant C :=
  mul_pos (by norm_num) (ThreeSlopePositiveActivity.lower_constant_pos C)

theorem article_14_1 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      ∃ pe pl : FinitePairDeficitInputs.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 32)) →
      FinitePairDeficitInputs.Hypotheses pe (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      FinitePairDeficitInputs.Hypotheses pl (GeneralGraphHostCount.sizeCap (1 / 30720)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤ thirdFactorialCumulant (dyadicBlock N) L ∧
          thirdFactorialCumulant (dyadicBlock N) L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Q, hQ, p, pe, hu⟩ := SharpThirdActivityUnderInputs.uniform_cumulant c κ hc hBCN C ε hε
  obtain ⟨Ds, k, k₁, k₂, hDs, hl⟩ := SharpThirdCumulantLowerUnderInputs.article_14_5 C
  refine ⟨Q, hQ, p, pe, ⟨Ds, k, k₁, k₂, hDs⟩, ?_⟩
  intro hgeo hgeoE hgeoL
  obtain ⟨NU, _hNU, hU⟩ := hu hgeo hgeoE
  obtain ⟨NL, _hNL, hL⟩ := hl hgeoL.source hgeoL.ordinaryTwo hgeoL.ordinaryThree
    hgeoL.sourceCurves hgeoL.ordinaryTwoCurves hgeoL.ordinaryThreeCurves
  refine ⟨max 10 (max NU NL), by omega, ?_⟩
  intro N hN L hcrit
  exact ⟨(hL N (by omega) L hcrit).2.2,
    (le_abs_self _).trans (hU N (by omega) L hcrit (dyadicBlock N) Subset.rfl)⟩

end PaperP1.OptimalThirdCumulantUnderInputs
