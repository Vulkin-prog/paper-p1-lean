module

public import PaperP1.Model.AlignedTripleFamilies
public import PaperP1.Model.ConnectedWindowFamilies
public import Mathlib.Tactic.Push

/-! # Actual connected triples split into aligned and nonaligned populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleJointPopulations

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

local instance tripleJointPopulationsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def nonalignedFamilies (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  (connectedFamilies G L 3).filter fun I ↦ ¬ AlignedTripleFamilies.AlignedFamily L I

def nonalignedJointMass (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ I ∈ nonalignedFamilies G L, infiniteJointMoment L I

def connectedJointMass (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ I ∈ connectedFamilies G L 3, infiniteJointMoment L I

theorem nonaligned_data {G I : Finset ℕ} {L : ℕ} (hI : I ∈ nonalignedFamilies G L) :
    I ⊆ G ∧ I.card = 3 ∧
      ∃ x ∈ I, ∃ y ∈ I, x ≠ y ∧ ¬ CompressedTargetAlignment.Aligned 1 x y L := by
  obtain ⟨hconn, hnon⟩ := mem_filter.mp hI
  obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hconn).1
  refine ⟨hIG, hcard, ?_⟩
  unfold AlignedTripleFamilies.AlignedFamily at hnon
  push Not at hnon
  exact hnon

theorem nonaligned_count_le (G : Finset ℕ) (L : ℕ) :
    (nonalignedFamilies G L).card ≤ (connectedFamilies G L 3).card := card_filter_le _ _

theorem split_bound (G : Finset ℕ) (L : ℕ) :
    connectedJointMass G L ≤ AlignedTripleFamilies.jointMass G L + nonalignedJointMass G L := by
  have hsplit := sum_filter_add_sum_filter_not (connectedFamilies G L 3)
    (AlignedTripleFamilies.AlignedFamily L) (infiniteJointMoment L)
  have haligned : (∑ I ∈ (connectedFamilies G L 3).filter (AlignedTripleFamilies.AlignedFamily L),
      infiniteJointMoment L I) ≤ AlignedTripleFamilies.jointMass G L := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro I hI
      obtain ⟨hconn, halign⟩ := mem_filter.mp hI
      have hdata := mem_powersetCard.mp (mem_filter.mp hconn).1
      exact AlignedTripleFamilies.mem_families.mpr ⟨hdata.1, hdata.2, halign⟩
    · intro I _ _
      exact infiniteJointMoment_nonneg L I
  change _ + nonalignedJointMass G L = connectedJointMass G L at hsplit
  linarith only [hsplit, haligned]

end PaperP1.TripleJointPopulations
