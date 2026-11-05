module

public import PaperP1.Algebra.TotalDegreeMonomialCardinality
public import PaperP1.Analysis.ActualLocalUnitMapGridCount

/-! # Exact height exponent and polynomial exceptional budget for the monomial family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonomialCountingParameters

open TotalDegreeMonomials TotalDegreeMonomialFamily


theorem height_exponent (k : ℕ) (hk : 1 ≤ k) :
    let n := Fintype.card (Index k)
    ((((k * n : ℕ) : ℝ)) / ((n * (n - 1) / 2 : ℕ) : ℝ)) = 4 / ((k : ℝ) + 3) := by
  let n := Fintype.card (Index k)
  let v := n * (n - 1) / 2
  have hn : 2 ≤ n := UnitMonomialEvaluationDeterminant.index_card_two_le k hk
  obtain ⟨hv, htri⟩ := LocalDeterminantDegreeChoice.triangle_weight n hn
  have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < (n : ℝ) - 1 := by linarith only [hnR]
  have hsize : (2 : ℝ) * (n : ℝ) = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    exact_mod_cast TotalDegreeMonomialCardinality.card_twice k
  have hm : (2 : ℝ) * ((n : ℝ) - 1) = (k : ℝ) * ((k : ℝ) + 3) := by nlinarith only [hsize]
  change (((k * n : ℕ) : ℝ) / (v : ℝ)) = _
  calc
    _ = 2 * (k : ℝ) / ((n : ℝ) - 1) := by
      apply (div_eq_div_iff hvR.ne' hnp.ne').mpr
      push_cast
      nlinarith only [congrArg (fun x : ℝ ↦ (k : ℝ) * x) htri]
    _ = 4 / ((k : ℝ) + 3) := by
      apply (div_eq_div_iff hnp.ne' (by positivity : (k : ℝ) + 3 ≠ 0)).mpr
      nlinarith only [hm]

theorem exceptional_budget (k : ℕ) :
    30 * ((Fintype.card (Index k) - 1) + 2) ^ 2 + 3 * (k + 1) ^ 6 ≤ 123 * (k + 1) ^ 6 := by
  have hcard := index_card_le k
  have hbase : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hmargin : (Fintype.card (Index k) - 1) + 2 ≤ 2 * (k + 1) ^ 2 := by omega
  have hsquare := Nat.pow_le_pow_left hmargin 2
  have hpower : (k + 1) ^ 4 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : (2 * (k + 1) ^ 2) ^ 2 = 4 * (k + 1) ^ 4 := by ring
  rw [he] at hsquare
  nlinarith only [hsquare, hpower]

end PaperP1.MonomialCountingParameters
