module

public import PaperP1.Asymptotics.TwoProgressionSublinear
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Uniform residual rank under the full enlarged geometric alignment convention -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedAlignedResidual

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.EnlargedPairGeometry PaperP1.TwoProgressionPrimeRows PaperP1.CriticalBandScale

theorem row_rank_sublinear (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      Geometric a b x y L →
      (Module.finrank F₂ (CoverGraphResolution.rowSolutions
        (PrimeRowComponents.rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))) : ℝ) ≤
          ε * ((L + 1 : ℕ) : ℝ) := by
  let c : ℝ := 1 / (2 * upperScale)
  have hc : 0 < c := by dsimp [c]; exact div_pos zero_lt_one (mul_pos (by norm_num) upperScale_pos)
  obtain ⟨Bcore, hcore⟩ := TwoProgressionSublinear.row_rank_sublinear c 13 1 2 ε 6 hc (by norm_num) hε
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C Bcore
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C 32 (by norm_num) 4
  refine ⟨max Ngeom Npoly, ?_⟩
  intro N hN L a b x y hcrit ha hab hheight hx hy halign
  let B : ℕ := L + 1
  change b ≤ B ^ 3 at hheight
  obtain ⟨hNtwo, hBcore, hBtwo, hBN, hBlo, hBhi⟩ := hgeom N ((le_max_left _ _).trans hN) L hcrit
  have hpolyNat : 32 * B ^ 4 < N := by exact_mod_cast hpoly N ((le_max_right _ _).trans hN) L hcrit
  have hBp : 1 ≤ B ^ 4 := by have h := pow_pos (show 0 < B by omega) 4; omega
  have hradius := radius_height hheight
  change radius b L ≤ 3 * B ^ 4 at hradius
  have hrad8 := Nat.mul_le_mul_left 8 hradius
  have hlarge : 8 * radius b L + 8 ≤ N := by nlinarith only [hrad8, hpolyNat, hBp]
  have hb : 0 < b := ha.trans_le hab
  have hxN := (mem_Ico.mp hx).1
  have hyN := (mem_Ico.mp hy).1
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hbase := base_geometry hb hxN hlarge
  let U : ℕ := base b x L
  let R : ℕ := 2 * radius b L
  have hRpos : 0 < radius b L := by unfold radius; positivity
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hU : 2 * R ≤ U := by dsimp [R, U]; nlinarith only [hbase.2.2]
  have hlogU : c * B ≤ Real.log U := CriticalWindowGeometry.log_base_lower (by omega : 4 ≤ N) hbase.2.1 hBhi
  have hlogR := logarithmic_width hBtwo hb hheight
  have hcoeff : b * a ≤ B ^ 6 := by
    have hmul := Nat.mul_le_mul hheight (hab.trans hheight)
    have hpowers : B ^ 3 * B ^ 3 = B ^ 6 := by ring
    nlinarith only [hmul, hpowers]
  apply hcore B hBcore (NormalizedWindowSets.union a b x y L)
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

theorem full_rank_sublinear (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      Geometric a b x y L →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
        ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Ncore, hcore⟩ := row_rank_sublinear C ε hε
  refine ⟨Ncore, ?_⟩
  intro N hN L a b x y hcrit ha hab hheight hx hy halign
  have hrow := hcore N hN L a b x y hcrit ha hab hheight hx hy halign
  have hle : (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
      Module.finrank F₂ (CoverGraphResolution.rowSolutions
        (PrimeRowComponents.rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))) := by
    exact_mod_cast Submodule.finrank_mono
      (FiniteResidualRank.kernel_le_rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))
  exact hle.trans hrow

end PaperP1.EnlargedAlignedResidual
