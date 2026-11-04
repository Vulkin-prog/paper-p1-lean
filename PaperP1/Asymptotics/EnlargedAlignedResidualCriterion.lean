module

public import PaperP1.Asymptotics.TwoProgressionSublinear
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # A base-sensitive residual row-rank criterion for the full enlarged alignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedAlignedResidualCriterion

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.EnlargedPairGeometry PaperP1.TwoProgressionPrimeRows

theorem row_rank_sublinear_of_geometry (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ L a b x y : ℕ, max B₀ 2 ≤ L + 1 →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → 32 * (L + 1) ^ 4 < x → 0 < y →
      2 * Real.log 2 ≤ Real.log x → c * (L + 1 : ℕ) ≤ Real.log x / 2 →
      Geometric a b x y L →
      (Module.finrank F₂ (CoverGraphResolution.rowSolutions
        (PrimeRowComponents.rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))) : ℝ) ≤
          ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Bcore, hcore⟩ := TwoProgressionSublinear.row_rank_sublinear c 13 1 2 ε 6 hc (by norm_num) hε
  refine ⟨Bcore, ?_⟩
  intro L a b x y hBcore ha hab hheight hpolyNat hypos hlogLarge hlogWidth halign
  let B : ℕ := L + 1
  change max Bcore 2 ≤ B at hBcore
  change b ≤ B ^ 3 at hheight
  change 32 * B ^ 4 < x at hpolyNat
  have hBtwo : 2 ≤ B := (le_max_right _ _).trans hBcore
  have hBp : 1 ≤ B ^ 4 := by have h := pow_pos (show 0 < B by omega) 4; omega
  have hradius := radius_height hheight
  change radius b L ≤ 3 * B ^ 4 at hradius
  have hrad8 := Nat.mul_le_mul_left 8 hradius
  have hlarge : 8 * radius b L + 8 ≤ x := by nlinarith only [hrad8, hpolyNat, hBp]
  have hb : 0 < b := ha.trans_le hab
  have hxpos : 0 < x := by omega
  have hxr : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hbase := base_geometry hb (le_refl x) hlarge
  let U : ℕ := base b x L
  let R : ℕ := 2 * radius b L
  have hRpos : 0 < radius b L := by unfold radius; positivity
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hU : 2 * R ≤ U := by dsimp [R, U]; nlinarith only [hbase.2.2]
  have hlogU : c * B ≤ Real.log U := by
    have hhalf : (x : ℝ) / 2 ≤ U := by
      have h : (x : ℝ) ≤ 2 * U := by exact_mod_cast hbase.2.1
      linarith
    have hmono := Real.log_le_log (by positivity : 0 < (x : ℝ) / 2) hhalf
    rw [Real.log_div hxr.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    change c * B ≤ Real.log x / 2 at hlogWidth
    linarith only [hmono, hlogLarge, hlogWidth]
  have hlogR := logarithmic_width hBtwo hb hheight
  have hcoeff : b * a ≤ B ^ 6 := by
    have hmul := Nat.mul_le_mul hheight (hab.trans hheight)
    have hpowers : B ^ 3 * B ^ 3 = B ^ 6 := by ring
    nlinarith only [hmul, hpowers]
  apply hcore B ((le_max_left _ _).trans hBcore) (NormalizedWindowSets.union a b x y L)
    B b a (x - 1) (y - 1) L L U R
  · exact le_rfl
  · simp only [one_mul, le_refl]
  · exact hb
  · exact ha
  · exact hcoeff
  · omega
  · omega
  · rw [NormalizedWindowSets.union, NormalizedPairGeometry.normalized_progression hxpos,
      NormalizedPairGeometry.normalized_progression hypos]
  · intro n hn
    exact (interval_bounds hab hxpos hypos halign hbase.1 n hn).1
  · intro n hn
    exact (interval_bounds hab hxpos hypos halign hbase.1 n hn).2
  · exact hR
  · exact hU
  · exact hlogU
  · exact hlogR
  · exact_mod_cast NormalizedPairGeometry.union_card_le (L := L) ha hb hxpos hypos

end PaperP1.EnlargedAlignedResidualCriterion
