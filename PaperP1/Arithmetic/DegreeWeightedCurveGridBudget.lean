module

public import PaperP1.Arithmetic.CurveFromCompleteRelations

/-! # Retaining the degree factor in the actual common-curve grid budget

The exact fibre lower count is divided by the positive maximum partial
degree. No point-count estimate is assumed by this finite comparison.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeWeightedCurveGridBudget

open Polynomial Arithmetic CompleteRelationWordEmbedding FreeComponentRank ShortBasisActualSpace CurveFromCompleteRelations
  BivariateDegrees BivariateTotalDegree CurveIntegerFibres

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : CommRing ℤ[X][X] := inferInstance

theorem rank_budget (x y L : ℕ) (cert : ShortBasisActualSpace.Certificate x y L)
    (curve : CommonCurveTheorem.Certificate (wordSpace x y L cert)) :
    (Module.finrank F₂ cert.space : ℝ) ≤
      ((integerGrid curve.polynomial (L + 1)).card : ℝ) /
        ((max (degreeX curve.polynomial) (degreeY curve.polynomial) : ℕ) : ℝ) +
      1 + 6 * (totalDegree curve.polynomial : ℝ) ^ 2 := by
  let d := max (degreeX curve.polynomial) (degreeY curve.polynomial)
  let t := Module.finrank F₂ cert.space
  let r := 1 + 6 * totalDegree curve.polynomial ^ 2
  have hd : 1 ≤ d :=
    (show 1 ≤ degreeX curve.polynomial by have hh := curve.degreeX_pos; omega).trans (le_max_left _ _)
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hg := actual_grid_bound x y L cert curve
  change d * (t - 1 - 6 * totalDegree curve.polynomial ^ 2) ≤ (integerGrid curve.polynomial (L + 1)).card at hg
  have hr : (r : ℝ) = 1 + 6 * (totalDegree curve.polynomial : ℝ) ^ 2 := by dsimp only [r]; push_cast; rfl
  have hpos : 0 ≤ ((integerGrid curve.polynomial (L + 1)).card : ℝ) / d := by positivity
  change (t : ℝ) ≤ ((integerGrid curve.polynomial (L + 1)).card : ℝ) / d + 1 + 6 * (totalDegree curve.polynomial : ℝ) ^ 2
  by_cases htr : t ≤ r
  · have hh : (t : ℝ) ≤ r := by exact_mod_cast htr
    linarith only [hh, hr, hpos]
  · have hrt : r ≤ t := by omega
    have he : t - 1 - 6 * totalDegree curve.polynomial ^ 2 = t - r := by dsimp only [r]; omega
    rw [he] at hg
    have hgr : (d : ℝ) * ((t : ℝ) - r) ≤ (integerGrid curve.polynomial (L + 1)).card := by
      exact_mod_cast hg
    have hh : (t : ℝ) - r ≤ ((integerGrid curve.polynomial (L + 1)).card : ℝ) / d :=
      (le_div_iff₀ hdr).mpr (by nlinarith only [hgr])
    linarith only [hh, hr]

end PaperP1.DegreeWeightedCurveGridBudget
