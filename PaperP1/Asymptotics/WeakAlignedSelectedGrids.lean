module

public import PaperP1.Asymptotics.CriticalAlignedSelections
public import PaperP1.Asymptotics.SourceCurvePointCover
public import PaperP1.Arithmetic.TwoTargetSelectedGrids

/-! # Actual selected physical classes avoiding deleted units satisfy the complete geometric admissibility conditions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakAlignedSelectedGrids

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.TwoTargetWindowSections
  PaperP1.TwoTargetSelectedGrids PaperP1.TwoTargetUnitExclusion PaperP1.EnlargedPairGeometry

theorem admissible_swap {S T : Finset ℤ} {p : ℤ × ℤ} (h : SourceCurvePointCover.Admissible S T p) :
    SourceCurvePointCover.Admissible T S p.swap := by
  obtain ⟨hS, hT, hiS, hiT, hdirect⟩ := h
  exact ⟨hT, hS, hiT, hiS, hdirect.symm⟩

theorem uniform_admissible (C : ℝ) (k K : ℕ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      ∀ a b : ℕ, 0 < a → 0 < b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 → Geometric a b y z L →
      ∀ s : ℕ, ∀ A : Fin k → Finset (TwoTargetWindowSections.Coordinate s L), (∀ i, (A i).card ≤ K) →
      ∀ D : Finset (Fin (L + 1) × Fin (L + 1)),
        (NormalizedUnitCount.units a b y z L \ D).card ≤ 1 →
        (∀ i, ∀ v ∈ A i, v ∉ unitEndpoints D) →
        ∀ j : Fin 2, SourceCurvePointCover.Admissible (gridOffsets A j.rev) (gridOffsets A j)
          (if j = 0 then ((z : ℤ), (y : ℤ)) else ((y : ℤ), (z : ℤ))) := by
  obtain ⟨N₀, hN₀, hu⟩ := CriticalAlignedSelections.uniform_selected_directness C (k * K)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband y z hy hz a b ha hb haH hbH hgeom s A hsize D hremaining havoid
  have hy2 : 2 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  have hz2 : 2 ≤ z := by have h := (mem_Ico.mp hz).1; omega
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := by omega
  have hcard : (SelectedProportionalPairs.values (y : ℤ) (gridOffsets A 0)).card +
      (SelectedProportionalPairs.values (z : ℤ) (gridOffsets A 1)).card ≤ k * K := by
    rw [selected_values_eq hypos, selected_values_eq hzpos]
    exact (Nat.add_le_add card_image_le card_image_le).trans (indices_total_card_le A hsize)
  have h := hu N hN L hband y z hy hz a b ha hb haH hbH hgeom
    (SelectedProportionalPairs.values (y : ℤ) (gridOffsets A 0))
    (SelectedProportionalPairs.values (z : ℤ) (gridOffsets A 1))
    (values_subset hypos A 0) (values_subset hzpos A 1) hcard
    (normalized_overlap_le_one hypos hzpos A D hremaining havoid)
  have horiginal : SourceCurvePointCover.Admissible (gridOffsets A 0) (gridOffsets A 1) ((y : ℤ), (z : ℤ)) :=
    ⟨grid_positive hy2 A 0, grid_positive hz2 A 1, h⟩
  intro j
  fin_cases j
  · change SourceCurvePointCover.Admissible (gridOffsets A 1) (gridOffsets A 0) ((z : ℤ), (y : ℤ))
    exact admissible_swap horiginal
  · exact horiginal

end PaperP1.WeakAlignedSelectedGrids
