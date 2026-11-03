module

public import PaperP1.Model.CanonicalComponentWeights
public import PaperP1.Combinatorics.FinitePolymerRemainder

/-! # Actual centered components with the one-distinguished-pair contribution removed before the exponential bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualComponentRemainder

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ActualCanonicalComponents
  PaperP1.ConnectedWindowFamilies PaperP1.Affine

def higher (G : Finset ℕ) (L K : ℕ) (η : ℝ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun C ↦ 3 ≤ C.card ∧ C.card ≤ K ∧ Connected L C ∧
    (runCompatibleNullity L C : ℝ) ≤ η * L

def population (G : Finset ℕ) (L K : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  G.powersetCard 2 ∪ higher G L K η

def weight (L : ℕ) (u : ℝ) (I : Finset ℕ) : ℝ := u ^ I.card * |infiniteCenteredCoefficient L I|

theorem population_sum (G : Finset ℕ) (L K : ℕ) (η u : ℝ) :
    (∑ I ∈ population G L K η, weight L u I) =
      (∑ I ∈ G.powersetCard 2, weight L u I) + ∑ I ∈ higher G L K η, weight L u I := by
  classical
  apply sum_union
  apply disjoint_left.mpr
  intro I hI hJ
  have htwo := (mem_powersetCard.mp hI).2
  have hthree := (mem_filter.mp hJ).2.1
  omega

theorem finite_bound (G : Finset ℕ) (L K : ℕ) (hL : 0 < L) (η u : ℝ) (hu : 0 ≤ u)
    (E F : Finset (Finset ℕ)) (hE : E ⊆ G.powersetCard 2)
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ K ∧
      (runRelativeNullity L I : ℝ) ≤ η * L ∧ I ∉ E) :
    (∑ I ∈ F, weight L u I) ≤
      Real.exp ((∑ e ∈ G.powersetCard 2, weight L u e) + ∑ C ∈ higher G L K η, weight L u C) -
        1 - ∑ e ∈ E, weight L u e := by
  classical
  let FN := F.filter fun I ↦ infiniteCenteredCoefficient L I ≠ 0
  have heq : (∑ I ∈ FN, weight L u I) = ∑ I ∈ F, weight L u I := by
    rw [show FN = F.filter (fun I ↦ infiniteCenteredCoefficient L I ≠ 0) from rfl, sum_filter]
    apply sum_congr rfl
    intro I _hI
    by_cases hc : infiniteCenteredCoefficient L I = 0 <;> simp [weight, hc]
  rw [← heq, ← population_sum G L K η u]
  apply FinitePolymerRemainder.covered_bound FN (population G L K η) E
    (fun e he ↦ mem_union_left _ (hE he)) (weight L u) (weight L u)
    (fun C ↦ mul_nonneg (pow_nonneg hu _) (abs_nonneg _))
  intro I hI
  obtain ⟨hIF, hnonzero⟩ := mem_filter.mp hI
  obtain ⟨hIG, hne, hsize, hcap, hnot⟩ := hF I hIF
  refine ⟨blocks L I, ?_, union_blocks L I, ?_, ?_, (CanonicalComponentWeights.weighted_absolute_factor L hL I u).le⟩
  · intro C hC
    have hCI := block_subset L I C hC
    have htwo := nonzero_block_card L hL I C hnonzero hC
    by_cases hcard : C.card = 2
    · exact mem_union_left _ (mem_powersetCard.mpr ⟨hCI.trans hIG, hcard⟩)
    · apply mem_union_right
      refine mem_filter.mpr ⟨mem_powerset.mpr (hCI.trans hIG), by omega,
        (card_le_card hCI).trans hsize, block_connected L I C hC, ?_⟩
      have hcomp := runCompatibleNullity_le_relative L C
      have hmono := relativeNullityOn_mono (fun x ↦ PaperP1.Arithmetic.squareClassSpace x L) hCI
      change runRelativeNullity L C ≤ runRelativeNullity L I at hmono
      have hle : (runCompatibleNullity L C : ℝ) ≤ runRelativeNullity L I := by exact_mod_cast (hcomp.trans hmono)
      exact hle.trans hcap
  · by_contra hn
    have hz : blocks L I = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hu := union_blocks L I
    rw [hz, biUnion_empty] at hu
    exact hne.ne_empty hu.symm
  · intro e he heq
    have hu := union_blocks L I
    rw [heq, singleton_biUnion] at hu
    exact hnot (hu ▸ he)

end PaperP1.ActualComponentRemainder
