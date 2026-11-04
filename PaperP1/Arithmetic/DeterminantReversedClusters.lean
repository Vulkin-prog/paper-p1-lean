module

public import PaperP1.Arithmetic.DeterminantSignedBoxes

/-! # Exact pullback of every source interval after reversing both coordinate pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantReversedClusters

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantCoordinateFlip
  PaperP1.DeterminantRelativeIntervals PaperP1.DeterminantIntervalPartition

def reversedCluster (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) : Finset Quad :=
  S.filter (fun p ↦ intervalIndex M E D p.1.2 p.1.1 = k)

theorem image_reversedCluster (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) :
    (reversedCluster M D E k S).image coordinateFlip = cluster M E D k (S.image coordinateFlip) := by
  unfold reversedCluster cluster
  rw [filter_image]
  rfl

theorem reversedCluster_card (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) :
    (reversedCluster M D E k S).card = (cluster M E D k (S.image coordinateFlip)).card := by
  rw [← image_reversedCluster, card_image_of_injective _ coordinateFlip_injective]

theorem flipped_mem_cluster (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) (p : Quad)
    (hp : p ∈ reversedCluster M D E k S) : coordinateFlip p ∈ cluster M E D k (S.image coordinateFlip) := by
  rw [← image_reversedCluster]
  exact mem_image.mpr ⟨p, hp, rfl⟩

theorem flipped_cluster_nonempty (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad)
    (hS : (reversedCluster M D E k S).Nonempty) : (cluster M E D k (S.image coordinateFlip)).Nonempty := by
  obtain ⟨p, hp⟩ := hS
  exact ⟨coordinateFlip p, flipped_mem_cluster M D E k S p hp⟩

theorem reversed_partition (M : ℕ) (D E : ℝ) (S : Finset Quad)
    (hpartition : (S.image coordinateFlip).card =
      ∑ k ∈ intervalIndices M, (cluster M E D k (S.image coordinateFlip)).card) :
    S.card = ∑ k ∈ intervalIndices M, (reversedCluster M D E k S).card := by
  rw [← card_image_of_injective S coordinateFlip_injective, hpartition]
  apply sum_congr rfl
  intro k _
  exact (reversedCluster_card M D E k S).symm

end PaperP1.DeterminantReversedClusters
