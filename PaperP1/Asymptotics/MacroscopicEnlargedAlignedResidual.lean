module

public import PaperP1.Asymptotics.EnlargedAlignedResidualCriterion
public import PaperP1.Asymptotics.MacroscopicPolynomialScale

/-! # Macroscopic residual rank for all enlarged geometric alignments, including zero units -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicEnlargedAlignedResidual

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.CriticalBandScale
  PaperP1.EnlargedPairGeometry PaperP1.TwoProgressionPrimeRows PaperP1.MacroscopicIntervalGeometry

theorem row_rank_sublinear (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ starts M δ → 0 < y →
      Geometric a b x y L →
      (Module.finrank F₂ (CoverGraphResolution.rowSolutions
        (PrimeRowComponents.rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))) : ℝ) ≤
          ε * ((L + 1 : ℕ) : ℝ) := by
  let c : ℝ := δ / (2 * upperScale)
  have hc : 0 < c := div_pos hδ (mul_pos (by norm_num) upperScale_pos)
  obtain ⟨B₀, hB⟩ := PaperP1.EnlargedAlignedResidualCriterion.row_rank_sublinear_of_geometry c ε hc hε
  obtain ⟨MG, hG⟩ := uniform_geometry C δ (max B₀ 2) hδ
  obtain ⟨MP, hP⟩ := PaperP1.MacroscopicPolynomialScale.polynomial_lt_source C δ 32 hδ (by norm_num) 4
  refine ⟨max MG MP, ?_⟩
  intro M hM L a b x y hcrit ha hab hheight hx hy halign
  obtain ⟨hlarge, _hbase, hlogLarge, hlogWidth⟩ := hG M (by omega) L hcrit x hx
  have hpoly : 32 * (L + 1) ^ 4 < x := by exact_mod_cast hP M (by omega) L hcrit x hx
  exact hB L a b x y hlarge ha hab hheight hpoly hy hlogLarge hlogWidth halign

theorem full_rank_sublinear (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ starts M δ → 0 < y →
      Geometric a b x y L →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
        ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨M₀, h⟩ := row_rank_sublinear C δ ε hδ hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hab hheight hx hy halign
  have hrow := h M hM L a b x y hcrit ha hab hheight hx hy halign
  have hle : (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
      Module.finrank F₂ (CoverGraphResolution.rowSolutions
        (PrimeRowComponents.rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))) := by
    exact_mod_cast Submodule.finrank_mono
      (FiniteResidualRank.kernel_le_rows (NormalizedWindowSets.union a b x y L) (exceptionalPrimes (L + 1) b a))
  exact hle.trans hrow

end PaperP1.MacroscopicEnlargedAlignedResidual
