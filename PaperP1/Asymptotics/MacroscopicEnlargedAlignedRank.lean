module

public import PaperP1.Asymptotics.MacroscopicEnlargedAlignedResidual
public import PaperP1.Asymptotics.EnlargedAlignedRank

/-! # Actual macroscopic pair-rank bounds under the complete enlarged alignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicEnlargedAlignedRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.EnlargedPairGeometry
  PaperP1.MacroscopicIntervalGeometry

theorem units_residual_bound (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ starts M δ → y ∈ starts M δ →
      Geometric a b x y L →
      (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨M₀, h⟩ := PaperP1.MacroscopicEnlargedAlignedResidual.full_rank_sublinear C δ ε hδ hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hab hheight hx hy halign
  have hx2 := starts_pos (by omega : 2 ≤ M) hδ hx
  have hy2 := starts_pos (by omega : 2 ≤ M) hδ hy
  have hres := h M hM L a b x y hcrit ha hab hheight hx (by omega) halign
  have hfinite : (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
      Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by
    exact_mod_cast loss_le_units_add_residual_all ha (ha.trans_le hab) hx2 hy2
  linarith

theorem channel_bound (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → a.Coprime b → b ≤ (L + 1) ^ 3 →
      x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L →
      (pairLoss x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨MR, hR⟩ := units_residual_bound C δ (ε / 2) hδ (by positivity)
  obtain ⟨MG, hG⟩ := uniform_geometry C δ (Nat.ceil (2 / ε)) hδ
  refine ⟨max MR MG, ?_⟩
  intro M hM L a b x y hcrit ha hab hcop hheight hx hy halign
  obtain ⟨hBlarge, _hbase, _hlogLarge, _hlogWidth⟩ := hG M (by omega) L hcrit x hx
  have hxpos : 0 < x := by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega
  have hypos : 0 < y := by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega
  have hb : 0 < b := ha.trans_le hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hbound := hR M (by omega) L a b x y hcrit ha hab hheight hx hy halign
  have hcount := PaperP1.EnlargedAlignedRank.units_channel_bound (L := L) ha hb hcop hxpos hypos
  have hceil : 2 / ε ≤ ((Nat.ceil (2 / ε) : ℕ) : ℝ) := Nat.le_ceil _
  have hlarge : 2 / ε ≤ ((L + 1 : ℕ) : ℝ) := hceil.trans (by exact_mod_cast hBlarge)
  have hεB : 2 ≤ ε * ((L + 1 : ℕ) : ℝ) := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith only [h]
  have hinv : 1 / (b : ℝ) ≤ 1 := (div_le_one hbR).mpr hb1
  have hsplit : ((L + 1 : ℕ) : ℝ) / b = (L : ℝ) / b + 1 / b := by push_cast; ring
  rw [hsplit] at hcount
  linarith

theorem actual_intersection_bound (C δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → a.Coprime b → b ≤ (L + 1) ^ 3 →
      x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L →
      (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨M₀, h⟩ := channel_bound C δ ε hδ hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hab hcop hheight hx hy halign
  have hxpos : 0 < x := by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega
  have hypos : 0 < y := by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega
  have hinter : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact hinter.trans (h M hM L a b x y hcrit ha hab hcop hheight hx hy halign)

end PaperP1.MacroscopicEnlargedAlignedRank
