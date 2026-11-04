module

public import PaperP1.Arithmetic.TwoTargetSelectedGrids
public import PaperP1.Asymptotics.SourceCurvePointCover
public import PaperP1.Arithmetic.TwoPointSquareClasses
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Arbitrary selected grids inherit actual full-window even independence

This supplies geometric admissibility directly from regular full windows and
their actual disjoint even square-class spaces. No nonalignment is required.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedWindowAdmissibility

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PositiveLineOffsetRoots
  PaperP1.SelectedProportionalPairs

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem space_mono {S T : Finset ℕ} (hST : S ⊆ T) :
    FiniteEvenSquareClasses.space S ≤ FiniteEvenSquareClasses.space T := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    rw [FiniteEvenSquareClasses.space_eq_span S a ha,
      FiniteEvenSquareClasses.space_eq_span T a (hST ha)]
    apply Submodule.span_mono
    exact Set.image_mono hST
  · rw [not_nonempty_iff_eq_empty.mp hS, FiniteEvenSquareClasses.space_empty]
    exact bot_le

theorem full_values_independent (x L : ℕ) (hx : 0 < x)
    (hrank : Module.finrank F₂ (squareClassSpace x L) = L) :
    EvenIndependentValues.Independent (NormalizedWindowSets.values x L) := by
  apply (EvenIndependentValues.rank_iff _).mpr
  rw [NormalizedWindowSets.space_values, hrank, NormalizedWindowSets.card_values hx]
  omega

theorem selected_values_subset {x L : ℕ} (hx : 0 < x) (I : Finset (Fin (L + 1))) :
    values (x : ℤ) (integerOffsets I) ⊆ NormalizedWindowSets.values x L := by
  rw [TwoTargetSelectedGrids.integer_values_eq hx]
  intro n hn
  obtain ⟨u, _hu, rfl⟩ := mem_image.mp hn
  exact NormalizedWindowSets.mem_values.mpr ⟨u, rfl⟩

theorem admissible_mono {S T S' T' : Finset ℤ} {p : ℤ × ℤ}
    (h : SourceCurvePointCover.Admissible S' T' p) (hS : S ⊆ S') (hT : T ⊆ T') :
    SourceCurvePointCover.Admissible S T p := by
  have hvS : values p.1 S ⊆ values p.1 S' := image_subset_image hS
  have hvT : values p.2 T ⊆ values p.2 T' := image_subset_image hT
  exact ⟨fun z hz ↦ h.1 z (hS hz), fun z hz ↦ h.2.1 z (hT hz),
    h.2.2.1.mono hvS, h.2.2.2.1.mono hvT,
    h.2.2.2.2.mono (space_mono hvS) (space_mono hvT)⟩

theorem admissible {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hrankx : Module.finrank F₂ (squareClassSpace x L) = L)
    (hranky : Module.finrank F₂ (squareClassSpace y L) = L)
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (I J : Finset (Fin (L + 1))) :
    SourceCurvePointCover.Admissible (integerOffsets I) (integerOffsets J) ((x : ℤ), (y : ℤ)) := by
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hI := selected_values_subset hxpos I
  have hJ := selected_values_subset hypos J
  have hspaceI : FiniteEvenSquareClasses.space (values (x : ℤ) (integerOffsets I)) ≤ squareClassSpace x L := by
    rw [← NormalizedWindowSets.space_values]
    exact space_mono hI
  have hspaceJ : FiniteEvenSquareClasses.space (values (y : ℤ) (integerOffsets J)) ≤ squareClassSpace y L := by
    rw [← NormalizedWindowSets.space_values]
    exact space_mono hJ
  refine ⟨?_, ?_, (full_values_independent x L hxpos hrankx).mono hI,
    (full_values_independent y L hypos hranky).mono hJ, hdirect.mono hspaceI hspaceJ⟩
  · intro z hz
    obtain ⟨u, _hu, rfl⟩ := mem_image.mp hz
    dsimp [integerOffset]
    omega
  · intro z hz
    obtain ⟨u, _hu, rfl⟩ := mem_image.mp hz
    dsimp [integerOffset]
    omega

end PaperP1.SelectedWindowAdmissibility
