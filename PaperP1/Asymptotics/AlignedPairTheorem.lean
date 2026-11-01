module

public import PaperP1.Asymptotics.AlignedPairRank
public import PaperP1.Asymptotics.FixedHeightResidual

/-! # One-unit subcase of T1.9, including fixed-height enlarged-prime residuals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedPairTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.IntervalResidualKernel

def UniformConclusion (C ε : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L a b x y : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < a → a ≤ b → a.Coprime b → b ≤ (L + 1) ^ 3 →
    x ∈ dyadicBlock N → y ∈ dyadicBlock N → (units a b x y L).Nonempty →
    (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) + ε * ((L + 1 : ℕ) : ℝ) ∧
    (pairLoss x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ) ∧
    (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ)

def FixedConclusion (Q : ℕ) (D K C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L a b x y H : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < a → a ≤ b → b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
    2 * b * L ≤ H → (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
    ∀ i j : Fin (L + 1), b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j →
    (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
      K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ)

theorem uniform_bounds (C ε : ℝ) (hε : 0 < ε) : ∃ N₀, UniformConclusion C ε N₀ := by
  obtain ⟨Nunit, hunit⟩ := AlignedPairRank.units_residual_bound C ε hε
  obtain ⟨Nchannel, hchannel⟩ := AlignedPairRank.channel_bound C ε hε
  refine ⟨max Nunit (max Nchannel 2), ?_⟩
  intro N hN L a b x y hcrit ha hab hcop hheight hx hy hunits
  have hu := hunit N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hheight hx hy hunits
  have hc := hchannel N ((le_max_left Nchannel 2).trans ((le_max_right _ _).trans hN))
    L a b x y hcrit ha hab hcop hheight hx hy hunits
  have hNtwo : 2 ≤ N := (le_max_right Nchannel 2).trans ((le_max_right _ _).trans hN)
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hle : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact ⟨hu, hc, hle.trans hc⟩

theorem fixed_height_loss (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N → (units a b x y L).Nonempty →
      (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hcore⟩ := FixedHeightResidual.full_kernel_rate Q hQ
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ncore, hNcore⟩ := hcore C
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L a b x y hcrit ha hab hbQ hx hy hunits
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hx2 : 2 ≤ x := hNtwo.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hNtwo.trans (mem_Ico.mp hy).1
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨u, hu⟩ := hunits
  have hres := hNcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hbQ hx hy u.1 u.2 (mem_units.mp hu)
  have hfinite : (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
      Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by
    exact_mod_cast loss_le_units_add_residual ha hb hx2 hy2 ⟨u, hu⟩
  linarith

theorem one_unit_T1_9 :
    (∀ C ε : ℝ, 0 < ε → ∃ N₀, UniformConclusion C ε N₀) ∧
    (∀ Q : ℕ, 1 ≤ Q → ∀ D : ℝ, 0 ≤ D →
      ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀, FixedConclusion Q D K C N₀) := by
  exact ⟨uniform_bounds, fun Q hQ D hD ↦ FixedHeightResidual.large_kernel_rate Q hQ D hD⟩

end PaperP1.AlignedPairTheorem
