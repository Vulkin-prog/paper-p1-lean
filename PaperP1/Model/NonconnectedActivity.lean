module

public import PaperP1.Model.ActualCanonicalComponents
public import PaperP1.Combinatorics.FinitePolymerTail
public import PaperP1.Model.CompatibleActivitySplit

/-! # A quadratic finite bound for all nonconnected centered activity at a fixed order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonconnectedActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

def families (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard r).filter (fun I ↦ ¬Connected L I)

def connectedBlocks (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) :=
  (Icc 2 r).biUnion (fun s ↦ connectedFamilies G L s)

def blockMass (G : Finset ℕ) (L r : ℕ) : ℝ :=
  ∑ C ∈ connectedBlocks G L r, |infiniteCenteredCoefficient L C|

theorem canonical_cover (G : Finset ℕ) (L r : ℕ) (hL : 0 < L) (hr : 1 ≤ r)
    (I : Finset ℕ) (hI : I ∈ families G L r) (hc : infiniteCenteredCoefficient L I ≠ 0) :
    ∃ P ⊆ connectedBlocks G L r, P.biUnion id = I ∧ 2 ≤ P.card ∧
      |infiniteCenteredCoefficient L I| ≤ ∏ C ∈ P, |infiniteCenteredCoefficient L C| := by
  classical
  obtain ⟨hIG, hconn⟩ := mem_filter.mp hI
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
  refine ⟨ActualCanonicalComponents.blocks L I, ?_, ActualCanonicalComponents.union_blocks L I,
    ActualCanonicalComponents.nonconnected_card L I (card_pos.mp (by omega)) hconn,
    (ActualCanonicalComponents.absolute_factor L hL I).le⟩
  intro C hC
  have hCI := ActualCanonicalComponents.block_subset L I C hC
  have hlow := ActualCanonicalComponents.nonzero_block_card L hL I C hc hC
  have hhigh : C.card ≤ r := (card_le_card hCI).trans_eq hcard
  exact mem_biUnion.mpr ⟨C.card, mem_Icc.mpr ⟨hlow, hhigh⟩,
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hCI.trans hsub, rfl⟩,
      ActualCanonicalComponents.block_connected L I C hC⟩⟩

theorem finite_bound (G : Finset ℕ) (L r : ℕ) (hL : 0 < L) (hr : 1 ≤ r) :
    CompatibleActivitySplit.absolute L (families G L r) ≤
      (blockMass G L r ^ 2 / 2) * Real.exp (blockMass G L r) := by
  classical
  let F := (families G L r).filter (fun I ↦ infiniteCenteredCoefficient L I ≠ 0)
  have heq : CompatibleActivitySplit.absolute L (families G L r) =
      ∑ I ∈ F, |infiniteCenteredCoefficient L I| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro I hI hnot
    have hz : infiniteCenteredCoefficient L I = 0 := by
      by_contra hn
      exact hnot (mem_filter.mpr ⟨hI, hn⟩)
    rw [hz, abs_zero]
  rw [heq]
  apply FinitePolymerTail.covered_bound F (connectedBlocks G L r)
    (fun I ↦ |infiniteCenteredCoefficient L I|) (fun C ↦ |infiniteCenteredCoefficient L C|)
    (fun _ ↦ abs_nonneg _)
  intro I hI
  obtain ⟨hI, hc⟩ := mem_filter.mp hI
  exact canonical_cover G L r hL hr I hI hc

theorem absolute_difference (G : Finset ℕ) (L r : ℕ) :
    CompatibleActivitySplit.absolute L (G.powersetCard r) -
      CompatibleActivitySplit.absolute L (connectedFamilies G L r) =
        CompatibleActivitySplit.absolute L (families G L r) := by
  classical
  have h := sum_filter_add_sum_filter_not (G.powersetCard r) (Connected L)
    (fun I ↦ |infiniteCenteredCoefficient L I|)
  change CompatibleActivitySplit.absolute L (connectedFamilies G L r) +
    CompatibleActivitySplit.absolute L (families G L r) = CompatibleActivitySplit.absolute L (G.powersetCard r) at h
  linarith only [h]

end PaperP1.NonconnectedActivity
