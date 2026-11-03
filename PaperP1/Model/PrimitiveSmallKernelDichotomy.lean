module

public import PaperP1.Asymptotics.FixedOrderAnchorMass
public import PaperP1.Arithmetic.SelectedAnchorRelation
public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Affine.PrimitiveCoordinateProjection
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Coding.RestrictedSupportRank

/-! # A primitive without a four-anchor certificate or saturated pair has many small coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveSmallKernelDichotomy

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.PhysicalWindowRelations PaperP1.FiniteFamilyEnumeration
  PaperP1.BinaryEvenSelections PaperP1.RankinSmallKernel PaperP1.Model.InfiniteStarts

local instance primitiveSmallKernelPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def smallOffsets (L : ℕ) (Y T : ℝ) (x : ℕ) : Finset (Fin (L + 1)) := by
  classical
  exact univ.filter fun i ↦ (truncatedKernel Y (x - 1 + i.val) : ℝ) ≤ T

def SaturatedPair (t L N : ℕ) (Y : ℝ) (I : Finset ℕ) : Prop :=
  ∃ x ∈ I, ∃ y ∈ I, PaperP1.MultiAnchorSaturation.Edge t (L + 1) N Y x y

theorem selected_alternative {t r L N : ℕ} (hN : 2 ≤ N) (I : Finset ℕ) (hcard : I.card = r)
    (hI : I ⊆ dyadicBlock N) (Y T : ℝ) (hY : (L + 1 : ℕ) ≤ Y)
    (a : I) (w : code (fun x : I ↦ x.val) L)
    (hheavy : t ≤ (selected (fun i ↦ w.val (a, i)) \ smallOffsets L Y T a.val).card) :
    PaperP1.FixedOrderAnchorMass.Covered t r (L + 1) N Y T I ∨ SaturatedPair t L N Y I := by
  classical
  let S := selected (fun i ↦ w.val (a, i)) \ smallOffsets L Y T a.val
  obtain ⟨V, hVS, hV⟩ := exists_subset_card_eq hheavy
  let e : Fin t ≃ V := (Finset.equivFinOfCardEq hV).symm
  let u : Fin t → Fin (L + 1) := fun i ↦ (e i).val
  have hu : Function.Injective u := Subtype.val_injective.comp e.injective
  have hwu : ∀ i, w.val (a, u i) ≠ 0 := by
    intro i
    exact (mem_filter.mp (mem_sdiff.mp (hVS (e i).property)).1).2
  have hlarge : ∀ i, T < (truncatedKernel Y (a.val - 1 + (u i).val) : ℝ) := by
    intro i
    have hnot := (mem_sdiff.mp (hVS (e i).property)).2
    exact lt_of_not_ge (fun h ↦ hnot (mem_filter.mpr ⟨mem_univ _, h⟩))
  let n := centres I hcard
  let a₀ := (enumeration I hcard).symm a
  let v : Fin r → Fin (L + 1) → F₂ := fun j i ↦ w.val (enumeration I hcard j, i)
  have ha : enumeration I hcard a₀ = a := (enumeration I hcard).apply_symm_apply a
  have hsum : (∑ j, ∑ i, v j i • parityVec (n j - 1 + i.val)) = 0 := by
    calc
      _ = ∑ j : I, ∑ i, w.val (j, i) • parityVec (j.val - 1 + i.val) :=
        Equiv.sum_comp (enumeration I hcard) _
      _ = ∑ j : I, vertexParityMap j.val L (fun i ↦ w.val (j, i)) := by
        apply sum_congr rfl
        intro j _
        rw [vertexParityMap_apply]
        simp only [startCompleteVertexLabel_eq_offset (show 0 < j.val by
          have hh := (mem_Ico.mp (hI j.property)).1
          omega)]
      _ = 0 := w.property.2
  obtain hc | ⟨j, hj⟩ := PaperP1.SelectedAnchorRelation.coordinate_alternative n
    (centres_mem (dyadicBlock N) I hcard hI) (centres_injective I hcard) Y T hY a₀ v u hu
    (by intro i; simpa only [v, ha] using hwu i)
    (by intro i; simpa only [n, centres, ha] using hlarge i) hsum
  · exact Or.inl ⟨n, centres_tupleSet I hcard, hc⟩
  · exact Or.inr ⟨a.val, a.property, n j, (enumeration I hcard j).property,
      by simpa only [n, centres, ha] using hj⟩

theorem sparse_projection {r L N : ℕ} (hN : 2 ≤ N) (I : Finset ℕ) (hcard : I.card = r)
    (hI : I ⊆ dyadicBlock N) (Y T : ℝ) (hY : (L + 1 : ℕ) ≤ Y)
    (hcovered : ¬ PaperP1.FixedOrderAnchorMass.Covered 4 r (L + 1) N Y T I)
    (hsaturated : ¬ SaturatedPair 4 L N Y I) (a : I) :
    Module.finrank F₂ (LinearMap.range (effectiveProjection (fun x : I ↦ x.val) L a)) ≤
      (smallOffsets L Y T a.val).card + 3 := by
  apply (effective_projection_rank_le (fun x : I ↦ x.val) L a).trans
  apply PaperP1.RestrictedSupportRank.finrank_bound
  intro v
  obtain ⟨w, hw⟩ := v.property
  have hword : (selected (fun i ↦ w.val (a, i)) \ smallOffsets L Y T a.val).card ≤ 3 := by
    by_contra h
    have hheavy : 4 ≤ (selected (fun i ↦ w.val (a, i)) \ smallOffsets L Y T a.val).card := by omega
    exact (selected_alternative hN I hcard hI Y T hY a w hheavy).elim hcovered hsaturated
  rw [← hw]
  change (selected (fun i ↦ w.val (a, i)) \ smallOffsets L Y T a.val).card ≤ 3
  exact hword

theorem primitive_nullity {r L N : ℕ} (hN : 2 ≤ N) (I : Finset ℕ) (hcard : I.card = r)
    (hI : I ⊆ dyadicBlock N) (Y T : ℝ) (hY : (L + 1 : ℕ) ≤ Y)
    (hprim : PaperP1.ConnectedWindowFamilies.Primitive L I)
    (hcovered : ¬ PaperP1.FixedOrderAnchorMass.Covered 4 r (L + 1) N Y T I)
    (hsaturated : ¬ SaturatedPair 4 L N Y I) (a : I) :
    runRelativeNullity L I ≤ (smallOffsets L Y T a.val).card + 3 := by
  have hdim := PaperP1.PrimitiveCoordinateProjection.finrank_range
    (fun x ↦ squareClassSpace x L) I hprim.2 a
  exact hdim.symm.trans_le (sparse_projection hN I hcard hI Y T hY hcovered hsaturated a)

end PaperP1.PrimitiveSmallKernelDichotomy
