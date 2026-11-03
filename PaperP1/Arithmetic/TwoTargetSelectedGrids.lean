module

public import PaperP1.Arithmetic.TwoTargetUnitExclusion
public import PaperP1.Arithmetic.CoefficientPatternGrids

/-! # Literal selected class grids preserve their actual window values and avoid every deleted unit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetSelectedGrids

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections
  PaperP1.TwoTargetClassOffsets PaperP1.PositiveLineOffsetRoots PaperP1.TwoTargetUnitExclusion
  PaperP1.FiniteEvenSquareClasses

def gridIndices {s L k : ℕ} (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    Finset (Fin (L + 1)) := univ.biUnion fun i ↦ targetIndices (C i) j

def gridOffsets {s L k : ℕ} (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    Finset ℤ := univ.biUnion fun i ↦ targetOffsets (C i) j

theorem grid_offsets_eq {s L k : ℕ} (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    gridOffsets C j = integerOffsets (gridIndices C j) := by
  ext z
  simp only [gridOffsets, gridIndices, targetOffsets, integerOffsets, mem_biUnion, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, u, hu, he⟩
    exact ⟨u, ⟨i, hu⟩, he⟩
  · rintro ⟨u, ⟨i, hu⟩, he⟩
    exact ⟨i, u, hu, he⟩

theorem vertex_cast {x L : ℕ} (hx : 0 < x) (i : Fin (L + 1)) :
    (startCompleteVertexLabel x L i : ℤ) = (x : ℤ) + integerOffset i :=
  NormalizedUnitCount.label_cast hx i

theorem integer_values_eq {x L : ℕ} (hx : 0 < x) (I : Finset (Fin (L + 1))) :
    SelectedProportionalPairs.values (x : ℤ) (integerOffsets I) = I.image (startCompleteVertexLabel x L) := by
  rw [SelectedProportionalPairs.values, integerOffsets, image_image]
  apply image_congr
  intro i _hi
  change ((x : ℤ) + integerOffset i).natAbs = startCompleteVertexLabel x L i
  rw [← vertex_cast hx i, Int.natAbs_natCast]

theorem selected_values_eq {s x L k : ℕ} (hx : 0 < x)
    (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    SelectedProportionalPairs.values (x : ℤ) (gridOffsets C j) =
      (gridIndices C j).image (startCompleteVertexLabel x L) := by
  rw [grid_offsets_eq, integer_values_eq hx]

theorem values_subset {s x L k : ℕ} (hx : 0 < x)
    (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    SelectedProportionalPairs.values (x : ℤ) (gridOffsets C j) ⊆ NormalizedWindowSets.values x L := by
  rw [selected_values_eq hx]
  intro n hn
  obtain ⟨i, _hi, rfl⟩ := mem_image.mp hn
  exact NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩

theorem grid_positive {s x L k : ℕ} (hx : 2 ≤ x)
    (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    ∀ z ∈ gridOffsets C j, 0 < (x : ℤ) + z := by
  rw [grid_offsets_eq]
  intro z hz
  obtain ⟨i, _hi, rfl⟩ := mem_image.mp hz
  dsimp [integerOffset]
  omega

theorem indices_total_card_le {s L k K : ℕ} (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L))
    (hK : ∀ i, (C i).card ≤ K) : (gridIndices C 0).card + (gridIndices C 1).card ≤ k * K := by
  have htotal (i : Fin k) : (targetIndices (C i) 0).card + (targetIndices (C i) 1).card ≤ K := by
    rw [← target_offsets_card, ← target_offsets_card]
    exact (total_card_le (C i)).trans (hK i)
  calc
    _ ≤ (∑ i : Fin k, (targetIndices (C i) 0).card) + ∑ i : Fin k, (targetIndices (C i) 1).card :=
      Nat.add_le_add card_biUnion_le card_biUnion_le
    _ = ∑ i : Fin k, ((targetIndices (C i) 0).card + (targetIndices (C i) 1).card) := sum_add_distrib.symm
    _ ≤ ∑ _i : Fin k, K := sum_le_sum (fun i _ ↦ htotal i)
    _ = _ := by simp

theorem avoids_deleted_units {s L k : ℕ} (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L))
    (D : Finset (Fin (L + 1) × Fin (L + 1)))
    (hC : ∀ i, ∀ v ∈ C i, v ∉ unitEndpoints D) :
    ∀ u ∈ D, u.1 ∉ gridIndices C 0 ∨ u.2 ∉ gridIndices C 1 := by
  intro u hu
  apply Or.inl
  intro hI
  obtain ⟨i, _hi, hui⟩ := mem_biUnion.mp hI
  apply hC i ((Sum.inr 0, u.1) : TwoTargetWindowSections.Coordinate s L)
    ((mem_target_indices _ _ _).mp hui)
  exact mem_union.mpr (Or.inl (mem_image.mpr ⟨u, hu, rfl⟩))

theorem normalized_overlap_le_one {s y z L k a b : ℕ} (hy : 0 < y) (hz : 0 < z)
    (C : Fin k → Finset (TwoTargetWindowSections.Coordinate s L))
    (D : Finset (Fin (L + 1) × Fin (L + 1)))
    (hremaining : (NormalizedUnitCount.units a b y z L \ D).card ≤ 1)
    (hC : ∀ i, ∀ v ∈ C i, v ∉ unitEndpoints D) :
    (dilate b (SelectedProportionalPairs.values (y : ℤ) (gridOffsets C 0)) ∩
      dilate a (SelectedProportionalPairs.values (z : ℤ) (gridOffsets C 1))).card ≤ 1 := by
  rw [selected_values_eq hy, selected_values_eq hz]
  exact selected_overlap_le_one (gridIndices C 0) (gridIndices C 1) D hremaining (avoids_deleted_units C D hC)

end PaperP1.TwoTargetSelectedGrids
