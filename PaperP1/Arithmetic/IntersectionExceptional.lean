module

public import PaperP1.Arithmetic.BranchingExceptional
public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Algebra.BinaryEvenSelections
public import PaperP1.Arithmetic.RelativeBlockRelations
public import PaperP1.Affine.MinimalRelativeRelations

/-! # An actual nonzero effective intersection forces a branching exception -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntersectionExceptional

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ConditionalWindowRank PaperP1.WindowRelationCode

local instance intersectionExceptionalPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem of_intersection {N L x : ℕ} {R : Finset ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N)
    {v : ℕ →₀ F₂} (hne : v ≠ 0) (hv : v ∈ squareClassSpace x L) (hold : v ∈ oldSpan R) :
    x ∈ BranchingExceptional.badStarts N L R := by
  classical
  have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
  rw [NormalizedWindowSets.squareClassSpace_eq_evenImage] at hv
  obtain ⟨w, hsum, hmap⟩ := (EvenImage.mem_image_iff _ _).mp hv
  have hmap' : windowParityMap (x - 1) (L + 1) w = v := by
    rw [EvenImage.combination_apply] at hmap
    simpa only [windowParityMap, Fintype.linearCombination_apply,
      startCompleteVertexLabel_eq_offset hxpos] using hmap
  have hselected : BinaryEvenSelections.selected w ⊆ supportedIndices R (x - 1) (L + 1) := by
    intro i hi
    by_contra hout
    exact (mem_filter.mp hi).2 (coefficient_zero_outside_pool w (hmap'.symm ▸ hold) i hout)
  let weven : LinearMap.ker (EvenSupportRank.sumMap F₂ (Fin (L + 1))) :=
    ⟨w, by simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using hsum⟩
  have hwen : weven ≠ 0 := by
    intro hz
    apply hne
    have hwz : w = 0 := congrArg Subtype.val hz
    simpa only [hwz, map_zero] using hmap'.symm
  exact mem_filter.mpr ⟨hx, (BinaryEvenSelections.selected_card_two hwen).trans (card_le_card hselected)⟩

theorem oldSpan_mono {R T : Finset ℕ} (hRT : R ⊆ T) : oldSpan R ≤ oldSpan T :=
  FiniteSetValueSpan.span_mono parityVec hRT

@[instance_reducible] def oldSpanFintype (R : Finset ℕ) : Fintype (oldSpan R) := by
  change Fintype (FiniteSetValueSpan.span (K := F₂) parityVec R)
  rw [FiniteSetValueSpan.span_eq_range]
  exact Fintype.ofSurjective (FiniteSetValueSpan.fullMap (K := F₂) parityVec R).rangeRestrict (by
    rintro ⟨z, ⟨w, hw⟩⟩
    exact ⟨w, Subtype.ext hw⟩)

theorem effective_le_raw {x L : ℕ} (hx : 0 < x) :
    squareClassSpace x L ≤ oldSpan (Ico (x - 1) (x + L)) := by
  rw [← NormalizedWindowSets.space_values, ← NormalizedWindowSets.values_eq_interval hx]
  exact RelativeBlockRelations.effective_le_full _

theorem span_le_raw (S : Finset ℕ) (L : ℕ) (hS : ∀ x ∈ S, 0 < x) :
    SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) S ≤ oldSpan (OldValuePrimeBudget.rawValues S L) := by
  apply iSup_le
  intro x
  exact (effective_le_raw (hS x.val x.property)).trans
    (oldSpan_mono (fun _ hn ↦ mem_biUnion.mpr ⟨x.val, x.property, hn⟩))

end PaperP1.IntersectionExceptional
