module

public import PaperP1.Asymptotics.EnlargedAlignedRank
public import PaperP1.Asymptotics.EnlargedFixedHeightResidual

/-! # T1.9 for the literal enlarged alignment, in both coefficient orientations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedAlignedPairTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.EnlargedPairGeometry
  PaperP1.IntervalResidualKernel

def UniformConclusion (C ε : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L a b x y : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < a → 0 < b → a.Coprime b → max a b ≤ (L + 1) ^ 3 →
    x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L →
    (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) + ε * ((L + 1 : ℕ) : ℝ) ∧
    (pairLoss x y L : ℝ) ≤ (L : ℝ) / max a b + ε * ((L + 1 : ℕ) : ℝ) ∧
    (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ (L : ℝ) / max a b + ε * ((L + 1 : ℕ) : ℝ)

def FixedConclusion (Q : ℕ) (D K C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L a b x y H : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < a → 0 < b → max a b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
    Geometric a b x y L → 2 * radius (max a b) L ≤ H → (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
    (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
      K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ)

theorem uniform_bounds (C ε : ℝ) (hε : 0 < ε) : ∃ N₀, UniformConclusion C ε N₀ := by
  obtain ⟨Nunit, hunit⟩ := EnlargedAlignedRank.units_residual_bound C ε hε
  obtain ⟨Nchannel, hchannel⟩ := EnlargedAlignedRank.channel_bound C ε hε
  refine ⟨max Nunit (max Nchannel 2), ?_⟩
  intro N hN L a b x y hcrit ha hb hcop hheight hx hy halign
  have hNunit : Nunit ≤ N := (le_max_left _ _).trans hN
  have hNchannel : Nchannel ≤ N := (le_max_left Nchannel 2).trans ((le_max_right _ _).trans hN)
  have hNtwo : 2 ≤ N := (le_max_right Nchannel 2).trans ((le_max_right _ _).trans hN)
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hpair : (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) + ε * ((L + 1 : ℕ) : ℝ) ∧
      (pairLoss x y L : ℝ) ≤ (L : ℝ) / max a b + ε * ((L + 1 : ℕ) : ℝ) := by
    by_cases hab : a ≤ b
    · have hheight' : b ≤ (L + 1) ^ 3 := (le_max_right _ _).trans hheight
      exact ⟨hunit N hNunit L a b x y hcrit ha hab hheight' hx hy halign,
        by simpa only [max_eq_right hab] using
          hchannel N hNchannel L a b x y hcrit ha hab hcop hheight' hx hy halign⟩
    · have hba : b ≤ a := le_of_not_ge hab
      have hheight' : a ≤ (L + 1) ^ 3 := (le_max_left _ _).trans hheight
      have hgeom := (geometric_swap a b x y L).mp halign
      rw [pairLoss_comm x y L, units_card_swap ha hb hxpos hypos]
      exact ⟨hunit N hNunit L b a y x hcrit hb hba hheight' hy hx hgeom,
        by simpa only [max_eq_left hba] using
          hchannel N hNchannel L b a y x hcrit hb hba hcop.symm hheight' hy hx hgeom⟩
  have hle : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact ⟨hpair.1, hpair.2, hle.trans hpair.2⟩

theorem fixed_height_residual (Q : ℕ) (hQ : 1 ≤ Q) (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀, FixedConclusion Q D K C N₀ := by
  obtain ⟨K, hK, hcore⟩ := EnlargedFixedHeightResidual.large_kernel_rate Q hQ D hD
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ncore, hNcore⟩ := hcore C
  refine ⟨Ncore, ?_⟩
  intro N hN L a b x y H hcrit ha hb hheight hx hy halign hcut hH
  by_cases hab : a ≤ b
  · rw [max_eq_right hab] at hcut
    exact hNcore N hN L a b x y H hcrit ha hab ((le_max_right _ _).trans hheight) hx hy halign hcut hH
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left hba] at hcut
    have hswap := hNcore N hN L b a y x H hcrit hb hba ((le_max_left _ _).trans hheight) hy hx
      ((geometric_swap a b x y L).mp halign) hcut hH
    have hrank : Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) =
        Module.finrank F₂ (largeKernel (NormalizedWindowSets.union b a y x L) H) := by
      exact congrArg (fun S : Finset ℕ ↦ Module.finrank F₂ (largeKernel S H)) (union_swap a b x y L)
    have hrankR : (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
        Module.finrank F₂ (largeKernel (NormalizedWindowSets.union b a y x L) H) := by exact_mod_cast hrank.le
    exact hrankR.trans hswap

theorem fixed_height_loss (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → 0 < b → max a b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L →
      (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hcore⟩ := EnlargedFixedHeightResidual.full_kernel_rate Q hQ
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ncore, hNcore⟩ := hcore C
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L a b x y hcrit ha hb hheight hx hy halign
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hx2 : 2 ≤ x := hNtwo.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hNtwo.trans (mem_Ico.mp hy).1
  have hres : (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
      K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
    by_cases hab : a ≤ b
    · exact hNcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab
        ((le_max_right _ _).trans hheight) hx hy halign
    · have hba : b ≤ a := le_of_not_ge hab
      rw [union_swap a b x y L]
      exact hNcore N ((le_max_left _ _).trans hN) L b a y x hcrit hb hba
        ((le_max_left _ _).trans hheight) hy hx ((geometric_swap a b x y L).mp halign)
  have hfinite : (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
      Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by
    exact_mod_cast loss_le_units_add_residual_all ha hb hx2 hy2
  linarith

theorem companion_T1_9 :
    (∀ C ε : ℝ, 0 < ε → ∃ N₀, UniformConclusion C ε N₀) ∧
    (∀ Q : ℕ, 1 ≤ Q → ∀ D : ℝ, 0 ≤ D →
      ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀, FixedConclusion Q D K C N₀) :=
  ⟨uniform_bounds, fixed_height_residual⟩

end PaperP1.EnlargedAlignedPairTheorem
