module

public import PaperP1.Model.TripleActivityConnected
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Asymptotics.LargeBoundaryTail

/-! # The independent part of all nonzero incompatible triple activities has the source decay -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncompatibleTripleSeed

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.FamilyIndependentMass

local instance incompatibleTripleSeedDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def families (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  (G.powersetCard 3).filter (fun I ↦ infiniteJointMoment L I = 0 ∧ infiniteCenteredCoefficient L I ≠ 0)

theorem subset_connected (G : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) : families G L ⊆ connectedFamilies G L 3 := by
  intro I hI
  obtain ⟨hsize, _, hc⟩ := mem_filter.mp hI
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hsize
  apply mem_filter.mpr
  exact ⟨hsize, TripleActivityConnected.connected_of_coefficient_ne_zero L hL I hcard
    (fun x hx ↦ hp x (hsub hx)) hc⟩

theorem activity_eq_active (G : Finset ℕ) (L : ℕ) :
    CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) =
      ∑ I ∈ families G L, |infiniteCenteredCoefficient L I| := by
  unfold CompatibleActivitySplit.incompatibleAbsolute families
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro I _
  by_cases hc : infiniteCenteredCoefficient L I = 0 <;> simp [hc]

theorem independent_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
        independentMass (families G L) L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) := by
  obtain ⟨NM, hNM⟩ := OriginalWindowFamilyMass.article_10_2 3 (by omega) C ε hε
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  refine ⟨max NM NL, ?_⟩
  intro N hN L G hband hG hp
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  have hmass := (hNM N (by omega) L G hband hG).2.2.1
  refine le_trans ?_ hmass
  apply sum_le_sum_of_subset_of_nonneg (subset_connected G L hL hp)
  intro I _ _
  exact prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L

end PaperP1.IncompatibleTripleSeed
