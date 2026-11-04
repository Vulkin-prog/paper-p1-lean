module

public import PaperP1.Asymptotics.NormalizedPairResidualCriterion
public import PaperP1.Asymptotics.MacroscopicIntervalGeometry

/-! # Uniform sublinear residual rank down to the actual macroscopic lower endpoint -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicNormalizedPairResidual

open PaperP1.Arithmetic PaperP1.Affine PaperP1.FiniteResidualRank PaperP1.CriticalBandScale
  PaperP1.MacroscopicIntervalGeometry

theorem rank_sublinear (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ starts M δ → 0 < y →
      ∀ i j : Fin (L + 1), b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j →
      (Module.finrank F₂ (valueKernel (PaperP1.NormalizedWindowSets.union a b x y L)) : ℝ) ≤ ε * (L + 1) := by
  let c : ℝ := δ / (2 * upperScale)
  have hc : 0 < c := div_pos hδ (mul_pos (by norm_num) upperScale_pos)
  obtain ⟨B₀, hB⟩ := PaperP1.NormalizedPairResidualCriterion.rank_sublinear_of_geometry c ε hc hε
  obtain ⟨M₀, hM₀⟩ := uniform_geometry C δ (max B₀ 2) hδ
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hab hheight hx hy i j hunit
  obtain ⟨hlarge, hbase, hlogLarge, hlogWidth⟩ := hM₀ M hM L hcrit x hx
  exact hB L a b x y hlarge ha hab hheight hbase hy hlogLarge hlogWidth i j hunit

end PaperP1.MacroscopicNormalizedPairResidual
